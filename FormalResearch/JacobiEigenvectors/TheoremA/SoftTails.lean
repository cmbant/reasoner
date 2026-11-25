module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftQuant

/-!
# Paper J, Layer 2 (L2.C7): the tails of the soft-edge eigenvector (chain step E6 of `PLAN.md`), `app_thmA` Step 4 (d)

Source: `app_thmA.tex`, "Proof of Proposition prop:tha-W2", Step 4 (d) `(S4tail)`: the sites outside the window `Omega = {|Z_n| <= rho}` contribute `<= C((1+A)^{-1/3} + h^{1/2})` times the mass of `Omega`, `A = max(-a,0)`.
The paper splits the sites outside `Omega` into three kinds: (i) parabolic-cylinder sites beyond the Airy layer (`SoftTails2.lean`, T3), (ii) left Weber sites
(`weber_tail`, T1), (iii) right Weber sites, the mirror of (ii) (`weber_tail_right`, T2).

## The exact chain of lemmas (every hypothesis is listed)

Notation as in `SoftQuant.lean`: `T_0 = |lam_L| / kappa_b`, `a = aOf`, `kappa_b = kappaBal a`.

* **T0' (abstract).**  `geom_up`, `geom_down`: `e >= 0`, `e_{n+1} <= theta e_n` (resp. `e_{n-1} <= theta e_n`), `0 <= theta < 1` give `sum e <= e_{n_0}/(1-theta)` (resp. `e_{n_1}/(1-theta)`).
* **T0 (abstract).**  `sq_sum_geom_le`: `f_n <= r f_{n+1}` on `0 <= n <= n_1`, `f >= 0`, `0 <= r < 1` give `sum_{n <= n_1} f_n^2 <= f_{n_1+1}^2 r^2/(1-r^2)`.
* **T1 (Weber tail, one chart), (ii).**  `weber_tail`: for a soft chart `C` (`ParabolicCylinderFacts`, `1 <= m`, `1 <= Lm`) and the exact solution `psi` seeded by `psi-hat^L_0`,
  `sum_{0 <= n <= n_1} E_Web(n)^2 M_Web(n)^2 <= C_w T_0^2 exp(-c_w/h)`, `n_1 = chainW.NR`.  Inputs: `growth_ratio`, `collar_lbW`, `propThaW2_item1`, `soft_env_psi`, `Eminus_left_small`.
* **T2 (Weber tail, right side), (iii).**  `weber_tail_right`: `weber_tail` for the mirror chart `CR` (`SoftMirror CL CR`), transported along `n -> N - n` (`sum_Icc_reflect`; inputs `uNode_mirror`,
  `aOf_mirror`, `shapeW` of `CR`), weighted by `|kappa-hat|` with the premise `|kappa-hat lam_R| <= C_k |lam_L|` (Step 4 (b); an explicit premise, as in `SoftQuant.lean`).
  The sites are the right Weber rows `{n in rowsOf N : u_n >= u_c + eta/2}`.  The constant is `max Cw 0`, so that the bound is monotone in `Cw`.
* **T3 (PC sites beyond the Airy layer), (i).**  `SoftTails2.lean`: `pc_tail_left` (`|u_n - u_c| < eta/2`, `Z_n < -rho`) and `pc_tail_right` (`Z_n > rho`, through the mirror chart).
* **T4 (assembly).**  `softEnv_eq`, `soft_tail`: not done (see *Not formalised*).

## Differences from the paper

* `weber_tail` and `weber_tail_right` are stated for the chart's own exact solution (`JacSol`) with the seed `psi-hat_0`; the paper's `psi^L`, `psi^R` are that solution.
* The Riemann-sum comparison of (i) is replaced by a geometric sum over consecutive sites, and the split at `|x| = eta/4` is not needed (`zeta_deriv` holds on all of `|x| <= 2 eta`); see `SoftTails2.lean`.

## Proved here

`sq_sum_geom_le`, `geom_up`, `geom_down`, `Mbal_le_one`, `Eminus_left_small`, `weber_tail` (T1), `sum_Icc_reflect`, `weber_tail_right` (T2).  Axioms pinned at the end of the file (`[propext, Classical.choice, Quot.sound]`).

## Not formalised

* T4: `softEnv_eq` (`softEnv = softEnvNum / softNorm`) and the relative form `(S4tail)` of `soft_tail`.  This needs the window-mass lower bound `sum_{Omega} V_n^2 >= c |lam_L|^2 kappa^{-2} h^{-1/2}`
  (`(S4mass)`, `PropThaWin` and `PropThaM`, plan items E3, E4), which is not a chart field and is not proved here; it would enter as an explicit premise.  The conversion of `V_n` to `E_- M` on the
  PC sites (`molv_upper`, `CPC`) and the sum of T1, T2, T3 are otherwise routine.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

/-! ### T0: the abstract geometric sum -/

/-- if `f_n <= r f_{n+1}` on `0 <= n <= n_1`, `f >= 0` there, `0 <= r < 1`, then `sum_{n=0}^{n_1} f_n^2 <= f_{n_1+1}^2 r^2/(1-r^2)`. -/
lemma sq_sum_geom_le (f : ℤ → ℝ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n1 : ℕ)
    (hf0 : ∀ n : ℤ, 0 ≤ n → n ≤ n1 → 0 ≤ f n) (hstep : ∀ n : ℤ, 0 ≤ n → n ≤ n1 → f n ≤ r * f (n + 1)) :
    ∑ n ∈ Finset.Icc (0 : ℤ) n1, f n ^ 2 ≤ f (n1 + 1) ^ 2 * (r ^ 2 / (1 - r ^ 2)) := by
  have hr2 : 0 < 1 - r ^ 2 := by nlinarith
  have key : ∀ k : ℕ, k ≤ n1 → ∑ n ∈ Finset.Icc (0 : ℤ) k, f n ^ 2 ≤ f (k + 1) ^ 2 * (r ^ 2 / (1 - r ^ 2)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 := hf0 0 le_rfl (by exact_mod_cast Nat.zero_le _)
      have h1 := hstep 0 le_rfl (by exact_mod_cast Nat.zero_le _)
      simp only [Nat.cast_zero, Finset.Icc_self, Finset.sum_singleton, zero_add] at h1 ⊢
      have h2 : f 0 ^ 2 ≤ (r * f 1) ^ 2 := pow_le_pow_left₀ h0 h1 2
      have h3 : r ^ 2 ≤ r ^ 2 / (1 - r ^ 2) := by
        rw [le_div_iff₀ hr2]; nlinarith [sq_nonneg r]
      calc f 0 ^ 2 ≤ (r * f 1) ^ 2 := h2
        _ = f 1 ^ 2 * r ^ 2 := by ring
        _ ≤ f 1 ^ 2 * (r ^ 2 / (1 - r ^ 2)) := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hk1 := hf0 ((k : ℤ) + 1) (by omega) (by exact_mod_cast hk)
      have hs := hstep ((k : ℤ) + 1) (by omega) (by exact_mod_cast hk)
      have e : (((k + 1 : ℕ) : ℤ)) = (k : ℤ) + 1 := by push_cast; ring
      have hI : Finset.Icc (0 : ℤ) ((k : ℤ) + 1) = insert ((k : ℤ) + 1) (Finset.Icc (0 : ℤ) k) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnm : ((k : ℤ) + 1) ∉ Finset.Icc (0 : ℤ) k := by simp
      rw [e, hI, Finset.sum_insert hnm, add_comm]
      have h2 : f ((k : ℤ) + 1) ^ 2 ≤ (r * f ((k : ℤ) + 1 + 1)) ^ 2 := pow_le_pow_left₀ hk1 hs 2
      have hA : ∑ n ∈ Finset.Icc (0 : ℤ) k, f n ^ 2 ≤ f ((k : ℤ) + 1) ^ 2 * (r ^ 2 / (1 - r ^ 2)) := by
        simpa using ih'
      have hB : f ((k : ℤ) + 1) ^ 2 * (r ^ 2 / (1 - r ^ 2)) + f ((k : ℤ) + 1) ^ 2 = f ((k : ℤ) + 1) ^ 2 * (1 / (1 - r ^ 2)) := by
        field_simp; ring
      calc ∑ n ∈ Finset.Icc (0 : ℤ) k, f n ^ 2 + f ((k : ℤ) + 1) ^ 2
          ≤ f ((k : ℤ) + 1) ^ 2 * (r ^ 2 / (1 - r ^ 2)) + f ((k : ℤ) + 1) ^ 2 := by linarith
        _ = f ((k : ℤ) + 1) ^ 2 * (1 / (1 - r ^ 2)) := hB
        _ ≤ (r * f ((k : ℤ) + 1 + 1)) ^ 2 * (1 / (1 - r ^ 2)) := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = f ((k : ℤ) + 1 + 1) ^ 2 * (r ^ 2 / (1 - r ^ 2)) := by ring
  exact key n1 le_rfl

/-- `M_bal <= 1` (`k_2 >= 1`). -/
lemma Mbal_le_one (a z : ℝ) : Mbal a z ≤ 1 := by
  unfold Mbal k2
  apply Real.rpow_le_one_of_one_le_of_nonpos _ (by norm_num)
  refine le_trans ?_ (le_max_right _ _)
  exact Real.one_le_rpow (le_max_right _ _) (by norm_num)

/-! ### T0': geometric decay along consecutive sites (for the PC tail (i)) -/

/-- (T0') geometric decay to the right: `e_{n+1} <= θ e_n` on `[n0, n1)` gives `∑_{[n0,n1]} e <= e_{n0}/(1-θ)`. -/
lemma geom_up (e : ℤ → ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (he0 : ∀ n, 0 ≤ e n) (n0 n1 : ℤ)
    (hup : ∀ n, n0 ≤ n → n < n1 → e (n + 1) ≤ θ * e n) :
    ∑ n ∈ Finset.Icc n0 n1, e n ≤ e n0 / (1 - θ) := by
  by_cases hle : n0 ≤ n1
  · have hpow : ∀ k : ℕ, n0 + k ≤ n1 → e (n0 + k) ≤ θ ^ k * e n0 := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have h2 := hup (n0 + k) (by omega) (by omega)
        have e1 : n0 + ((k + 1 : ℕ) : ℤ) = n0 + k + 1 := by push_cast; ring
        rw [e1]
        calc e (n0 + k + 1) ≤ θ * e (n0 + k) := h2
          _ ≤ θ * (θ ^ k * e n0) := mul_le_mul_of_nonneg_left h1 hθ0
          _ = θ ^ (k + 1) * e n0 := by ring
    have hsum : ∀ k : ℕ, n0 + k ≤ n1 → ∑ n ∈ Finset.Icc n0 (n0 + k), e n ≤ e n0 * ∑ j ∈ Finset.range (k + 1), θ ^ j := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have e1 : n0 + ((k + 1 : ℕ) : ℤ) = n0 + k + 1 := by push_cast; ring
        have hI : Finset.Icc n0 (n0 + k + 1) = insert (n0 + k + 1) (Finset.Icc n0 (n0 + k)) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnm : (n0 + k + 1) ∉ Finset.Icc n0 (n0 + k) := by simp
        rw [e1, hI, Finset.sum_insert hnm, Finset.sum_range_succ]
        have h1 := ih (by omega)
        have h2 := hpow (k + 1) (by omega)
        rw [e1] at h2
        calc e (n0 + k + 1) + ∑ n ∈ Finset.Icc n0 (n0 + k), e n ≤ θ ^ (k + 1) * e n0 + e n0 * ∑ j ∈ Finset.range (k + 1), θ ^ j := add_le_add h2 h1
          _ = e n0 * (∑ j ∈ Finset.range (k + 1), θ ^ j + θ ^ (k + 1)) := by ring
    have hk := hsum (n1 - n0).toNat (by omega)
    have e2 : n0 + ((n1 - n0).toNat : ℤ) = n1 := by omega
    rw [e2] at hk
    have hg : ∑ j ∈ Finset.range ((n1 - n0).toNat + 1), θ ^ j ≤ 1 / (1 - θ) := by
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := (n1 - n0).toNat + 1) hθ0 hθ1
      rw [← Finset.range_eq_Ico] at this
      simpa using this
    calc _ ≤ e n0 * ∑ j ∈ Finset.range ((n1 - n0).toNat + 1), θ ^ j := hk
      _ ≤ e n0 * (1 / (1 - θ)) := mul_le_mul_of_nonneg_left hg (he0 n0)
      _ = e n0 / (1 - θ) := by ring
  · rw [Finset.Icc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    exact div_nonneg (he0 n0) (by linarith)

/-- (T0') geometric decay to the left: `e_{n-1} <= theta e_n` on `(n0, n1]` gives `sum_{[n0,n1]} e <= e_{n1}/(1-theta)`. -/
lemma geom_down (e : ℤ → ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (he0' : ∀ n, 0 ≤ e n) (n0 n1 : ℤ)
    (hdn : ∀ n, n0 < n → n ≤ n1 → e (n - 1) ≤ θ * e n) :
    ∑ n ∈ Finset.Icc n0 n1, e n ≤ e n1 / (1 - θ) := by
  have h := geom_up (fun n => e (-n)) θ hθ0 hθ1 (fun n => he0' _) (-n1) (-n0) (by
    intro n hn1 hn2
    have := hdn (-n) (by omega) (by omega)
    have e1 : -(n + 1) = -n - 1 := by ring
    simpa [e1] using this)
  have hs : ∑ n ∈ Finset.Icc n0 n1, e n = ∑ n ∈ Finset.Icc (-n1) (-n0), e (-n) := by
    apply Finset.sum_nbij' (fun n => -n) (fun n => -n)
    · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
    · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
    · intro n _; ring
    · intro n _; ring
    · intro n _; simp
  rw [hs]
  simpa using h

/-! ### T1: the left Weber tail -/

section Left

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

section LeftAt

variable {μ : Par × ℝ} (hμ : μ ∈ P) {X : ℝ} (hX : |X - Fz.bandHi μ| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N)
  (hh : Fz.step N ≤ C.softH2) {lam : ℝ}
  (hV : ((C.chain μ X N).rescale1 lam).PreValid C.cs (Fz.step N) m)

include hμ hX hN hh hV

/-- **The left forbidden side is exponentially small**: for a row `j` with `-2 eta <= x_j <= -5 eta/16` (so on the recessive patch), `E_-(a, Z_j) <= exp(-c_Q/h)`
(`Eminus_decay` from `Z_j` to `zeta(-eta/4)/sqrt h`, where `Z^2/4 + a >= c_{z1}/(8h)`; `zeta(-eta/4) <= zeta(x_{j_2}) <= 0` by `j2_ge`). -/
lemma Eminus_left_small {j : ℤ} (hj1 : -(2 * C.η) ≤ uNode (Fz.step N) j - C.uc μ)
    (hj2 : uNode (Fz.step N) j - C.uc μ ≤ -(5 * C.η / 16)) :
    Eminus (C.aOf μ X N) (C.Zof μ X N j) ≤ Real.exp (-(softCQ C / Fz.step N)) := by
  have hhH1 : Fz.step N ≤ C.softH1 := hh.trans C.softH2_le_H1
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hμ hX hN hhH1 hV
  obtain ⟨-, hη, hdm, hdmp, -⟩ := C.consts_pos
  have hz1 := C.consts_pos2.2
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hs2 : Real.sqrt (Fz.step N) ^ 2 = Fz.step N := Real.sq_sqrt hh0.le
  have hα := C.abs_alpha_le hX
  have hj2ge := C.j2_ge hμ hX hN hh hV
  have hsucc := uNode_succ_sub' (Fz.step N) ((C.chain μ X N).jj 2)
  have hx2d : uNode (Fz.step N) ((C.chain μ X N).jj 2) - C.uc μ ≤ 2 * C.η := by linarith
  -- zeta(-eta/4) <= zeta(x_{j_2}) <= 0
  have hmv1 := C.zeta_mvt hμ hα (by linarith : -(2 * C.η) ≤ -(C.η / 4)) hj2ge hx2d
  have hζhat : C.zeta μ (Fz.bandHi μ - X) (-(C.η / 4)) ≤ 0 := by
    have := mul_nonneg hdm.le (sub_nonneg.mpr hj2ge)
    linarith [hmv1.1]
  -- zeta(x_j) + dm eta/16 <= zeta(-eta/4)
  have hmv2 := C.zeta_mvt hμ hα hj1 (by linarith : uNode (Fz.step N) j - C.uc μ ≤ -(C.η / 4)) (by linarith : -(C.η / 4) ≤ 2 * C.η)
  have hgap : C.dm * (C.η / 16) ≤ C.zeta μ (Fz.bandHi μ - X) (-(C.η / 4)) - C.zeta μ (Fz.bandHi μ - X) (uNode (Fz.step N) j - C.uc μ) := by
    have : C.dm * (C.η / 16) ≤ C.dm * (-(C.η / 4) - (uNode (Fz.step N) j - C.uc μ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hdm.le
    linarith [hmv2.1]
  set zh : ℝ := C.zeta μ (Fz.bandHi μ - X) (-(C.η / 4)) / Real.sqrt (Fz.step N) with hzh
  have hzh0 : zh ≤ 0 := div_nonpos_of_nonpos_of_nonneg hζhat hs.le
  have hZj : C.Zof μ X N j = C.zeta μ (Fz.bandHi μ - X) (uNode (Fz.step N) j - C.uc μ) / Real.sqrt (Fz.step N) := rfl
  have hz12 : C.Zof μ X N j ≤ zh := by
    rw [hZj, hzh]
    apply div_le_div_of_nonneg_right _ hs.le
    have : 0 ≤ C.dm * (C.η / 16) := by positivity
    linarith
  have hmar : (Real.sqrt (C.cz1 / 8) / Real.sqrt (Fz.step N)) ^ 2 ≤ zh ^ 2 / 4 + C.aOf μ X N := by
    have hq := C.Zq_lb hμ hX hhH1 (x := -(C.η / 4)) (by rw [abs_neg, abs_of_pos (by linarith)])
      (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
    have e : zh ^ 2 / 4 + C.aOf μ X N = (C.zeta μ (Fz.bandHi μ - X) (-(C.η / 4)) ^ 2 / 4 - C.muTilde μ X N) / Fz.step N := by
      rw [hzh, SoftEdgeCore.aOf_eq, div_pow, hs2]; field_simp; ring
    rw [e, div_pow, Real.sq_sqrt (by positivity), hs2]
    exact div_le_div_of_nonneg_right hq hh0.le
  have hdec := Eminus_decay (C.aOf μ X N) (Real.sqrt (C.cz1 / 8) / Real.sqrt (Fz.step N)) hz12 hzh0 (by positivity) hmar
  have hexp : softCQ C / Fz.step N ≤ Real.sqrt (C.cz1 / 8) / Real.sqrt (Fz.step N) * (zh - C.Zof μ X N j) := by
    have hdiff : C.dm * (C.η / 16) / Real.sqrt (Fz.step N) ≤ zh - C.Zof μ X N j := by
      rw [hZj, hzh, ← sub_div]
      exact div_le_div_of_nonneg_right hgap hs.le
    have hq0 : 0 ≤ Real.sqrt (C.cz1 / 8) / Real.sqrt (Fz.step N) := by positivity
    calc softCQ C / Fz.step N = Real.sqrt (C.cz1 / 8) / Real.sqrt (Fz.step N) * (C.dm * (C.η / 16) / Real.sqrt (Fz.step N)) := by
          rw [div_mul_div_comm, Real.mul_self_sqrt hh0.le]; unfold softCQ; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiff hq0
  have hone := Eminus_le_one (C.aOf μ X N) hzh0
  calc Eminus (C.aOf μ X N) (C.Zof μ X N j)
      ≤ Real.exp (-(Real.sqrt (C.cz1 / 8) / Real.sqrt (Fz.step N) * (zh - C.Zof μ X N j))) * Eminus (C.aOf μ X N) zh := hdec
    _ ≤ Real.exp (-(softCQ C / Fz.step N)) * 1 :=
        mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hone (Eminus_pos _ _).le (Real.exp_pos _).le
    _ = _ := mul_one _

end LeftAt

/-- **T1: the left Weber tail** (`app_thmA` Step 4 (d) (ii)).  For the exact solution `psi` seeded by `psi-hat^L_0`:
`sum_{0 <= n <= n_1} E_Web(n)^2 M_Web(n)^2 <= C_w (|lam_L|/kappa_b)^2 exp(-c_w/h)`, `n_1 = chainW.NR` the last row with `u_n <= u_c - eta/2`. -/
theorem weber_tail {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) :
    ∃ Cw cw h0 : ℝ, 0 < h0 ∧ 0 < cw ∧ ∀ p ∈ P, ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ C.δ0 →
      ∀ ψ : ℤ → ℝ, JacSol Fz p N X (C.chain p X N).NR ψ → ψ 0 = C.psiHatL p X N 0 →
        ∑ n ∈ Finset.Icc (0 : ℤ) (C.chainW p X N).NR, softEnvWeb C p X N n ^ 2 ≤
          Cw * (|C.lamL p X N| / kappaBal (C.aOf p X N)) ^ 2 * Real.exp (-(cw / Fz.step N)) := by
  obtain ⟨Cc, h0a, clam, Clam, h0apos, hclam, H1⟩ := propThaW2_item1 C hf hm hLm
  obtain ⟨CE, h0b, h0bpos, hCE, HE⟩ := soft_env_psi C hf hm hLm
  obtain ⟨hCA, hnu, hc3, hC2, hCM⟩ := C.consts_pos3
  obtain ⟨-, hη, -⟩ := C.consts_pos
  set γ : ℝ := C.nu1 / (C.CA + 1) with hγ
  have hγpos : 0 < γ := by positivity
  set r : ℝ := (1 + γ)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  set Kr : ℝ := r ^ 2 / (1 - r ^ 2) with hKr
  have hr2 : 0 < 1 - r ^ 2 := by nlinarith
  have hKr0 : 0 ≤ Kr := div_nonneg (sq_nonneg _) hr2.le
  set ε : ℝ := C.c3W / (2 * (|Cc| + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hcQ := softCQ_pos C
  refine ⟨(2 / C.c3W) ^ 2 * Kr * CE ^ 2, 2 * softCQ C,
    min h0a (min h0b (min C.softH2 (min (C.η / 16) (softHL C ε)))),
    lt_min h0apos (lt_min h0bpos (lt_min C.softH2_pos (lt_min (by positivity) (softHL_pos C ε)))), by positivity, ?_⟩
  intro p hp N hN hstep X hX ψ hJ hseed
  have hs0a : Fz.step N ≤ h0a := hstep.trans (min_le_left _ _)
  have hs0b : Fz.step N ≤ h0b := hstep.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs2 : Fz.step N ≤ C.softH2 := hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs16 : Fz.step N ≤ C.η / 16 :=
    hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hsLe : Fz.step N ≤ softHL C ε :=
    hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hhH1 : Fz.step N ≤ C.softH1 := hs2.trans C.softH2_le_H1
  have hh1 : Fz.step N ≤ 1 := hhH1.trans C.softH1_le_one
  have hVpre : ((C.chain p X N).rescale1 (softLam C p X N)).PreValid C.cs (Fz.step N) m := C.valid p hp X hX N hN
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hp hX hN hhH1 hVpre
  have hj2ge := C.j2_ge hp hX hN hs2 hVpre
  obtain ⟨-, -, hNW0, hNWu, hNWv⟩ := C.shapeW p hp X hX N hN
  have hsuccW := uNode_succ_sub' (Fz.step N) (C.chainW p X N).NR
  have hn1jj2 : (C.chainW p X N).NR < (C.chain p X N).jj 2 := by
    by_contra hcon
    have := SoftEdgeChart.uNode_mono_le hh0.le (not_lt.mp hcon)
    linarith
  have hn1NR : (C.chainW p X N).NR + 1 ≤ (C.chain p X N).NR := by omega
  have hArows := A_ne_zero_rows C hp hX hN hhH1 hVpre
  have hAeq := C.A_bond p hp X hX N hN
  have hApos : ∀ n : ℤ, 0 ≤ n → n ≤ (C.chainW p X N).NR → 0 < Fz.bondA p N n := by
    intro n hn0 hn1
    have hne := hArows n hn0 (by omega)
    rw [hAeq n (mem_Icc.mpr ⟨by omega, by omega⟩)] at hne
    exact lt_of_le_of_ne (bondA_nonneg' Fz p N n) (Ne.symm hne)
  have hAle : ∀ n : ℤ, 0 ≤ n → n ≤ (C.chainW p X N).NR → Fz.bondA p N n ≤ C.CA + 1 := fun n _ _ => by
    linarith [C.bondA_le p hp N hN n]
  have hgap : ∀ n : ℤ, 0 ≤ n → n ≤ (C.chainW p X N).NR →
      Fz.bondA p N n + Fz.bondA p N (n - 1) + C.nu1 ≤ Fz.diagQ p N X n := by
    intro n hn0 hn1
    refine C.grow_gap p hp X hX N hN n hn0 ?_
    have : uNode (Fz.step N) n ≤ uNode (Fz.step N) (C.chainW p X N).NR := SoftEdgeChart.uNode_mono_le hh0.le hn1
    linarith
  have hu0 : uNode (Fz.step N) 0 ≤ C.uc p - C.η / 2 := uNode_zero_le C hp (hs16.trans (by linarith))
  have hψ0pos : 0 < ψ 0 := by
    rw [hseed, psiHatL_of_le C p X N hu0]; exact C.seed_posW p hp X hX N hN
  have hA0 : Fz.bondA p N (-1) = 0 := by
    unfold SymbolFamily.bondA
    rw [ite_eq_right (by omega)]
  have hgr := growth_ratio (Fz.bondA p N) (Fz.diagQ p N X) ψ (C.chainW p X N).NR (C.CA + 1) C.nu1 hA0 hApos hAle hnu hgap
    (fun n hn0 hn1 => hJ n hn0 (by omega)) hψ0pos
  -- the lower bound `(c_3/2) V_n <= psi_n`
  obtain ⟨hmain, -, -⟩ := H1 p hp N hN hs0a X hX
  obtain ⟨hWeb, -⟩ := hmain ψ hJ hseed
  have hpow : Fz.step N ^ m * Lm (Fz.step N) ≤ ε := by
    have h1 : Fz.step N ^ m ≤ Fz.step N := pow_le_of_le_one hh0.le hh1 (by omega)
    have h2 : Fz.step N * Lm (Fz.step N) ≤ ε := softHL_spec C hεpos hh0 hsLe
    have h3 := Lm_nonneg C hh0 hh1
    exact (mul_le_mul_of_nonneg_right h1 h3).trans h2
  have hpow0 : 0 ≤ Fz.step N ^ m * Lm (Fz.step N) := powLm_nonneg C hh0 hh1
  have hCcε : |Cc| * ε ≤ C.c3W / 2 := by
    have : |Cc| * ε ≤ (|Cc| + 1) * ε := by nlinarith [abs_nonneg Cc]
    refine this.trans (le_of_eq ?_)
    rw [hε]; field_simp
  have hlow : ∀ n ∈ Finset.Icc (0 : ℤ) (C.chainW p X N).NR, softEnvWeb C p X N n ≤ (2 / C.c3W) * ψ n := by
    intro n hn
    obtain ⟨hn0, hn1⟩ := mem_Icc.mp hn
    have hun : uNode (Fz.step N) n ≤ C.uc p - C.η / 2 := by
      have := SoftEdgeChart.uNode_mono_le hh0.le hn1
      linarith
    have hV' : softEnvWeb C p X N n = (C.chainW p X N).W n * (C.chainW p X N).M n := by
      unfold softEnvWeb
      rw [C.W_defW p hp X hX N hN n hn, C.M_defW p hp X hX N hN n hn]
    have hcl := C.collar_lbW p hp X hX N hN n hn hun
    have hψpos := (hgr n hn0 hn1).1
    have herr := hWeb n (mem_Icc.mpr ⟨hn0, by omega⟩) hun
    rw [psiHatL_of_le C p X N hun] at herr
    have hVnn : 0 ≤ softEnvWeb C p X N n := softEnvWeb_nonneg C p X N n
    have h1 : C.c3W * softEnvWeb C p X N n ≤ |(C.chainW p X N).phi (Fz.step N) 0 1 n| := by
      rw [hV']; calc _ = C.c3W * (C.chainW p X N).W n * (C.chainW p X N).M n := by ring
        _ ≤ _ := hcl
    have h2 : |(C.chainW p X N).phi (Fz.step N) 0 1 n| ≤ ψ n + Cc * Fz.step N ^ m * Lm (Fz.step N) * softEnvWeb C p X N n := by
      have : |(C.chainW p X N).phi (Fz.step N) 0 1 n| ≤ |ψ n| + |ψ n - (C.chainW p X N).phi (Fz.step N) 0 1 n| := by
        calc _ = |ψ n - (ψ n - (C.chainW p X N).phi (Fz.step N) 0 1 n)| := by ring_nf
          _ ≤ |ψ n| + |ψ n - (C.chainW p X N).phi (Fz.step N) 0 1 n| := abs_sub _ _
      rw [abs_of_pos hψpos] at this
      linarith
    have h3 : Cc * Fz.step N ^ m * Lm (Fz.step N) * softEnvWeb C p X N n ≤ C.c3W / 2 * softEnvWeb C p X N n := by
      have : Cc * Fz.step N ^ m * Lm (Fz.step N) ≤ C.c3W / 2 := by
        calc Cc * Fz.step N ^ m * Lm (Fz.step N) = Cc * (Fz.step N ^ m * Lm (Fz.step N)) := by ring
          _ ≤ |Cc| * (Fz.step N ^ m * Lm (Fz.step N)) := mul_le_mul_of_nonneg_right (le_abs_self _) hpow0
          _ ≤ |Cc| * ε := mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
          _ ≤ _ := hCcε
      exact mul_le_mul_of_nonneg_right this hVnn
    have h4 : C.c3W / 2 * softEnvWeb C p X N n ≤ ψ n := by linarith
    rw [show 2 / C.c3W * ψ n = (2 * ψ n) / C.c3W by ring, le_div_iff₀ hc3]
    linarith
  -- the geometric sum
  obtain ⟨n1n, hn1n⟩ : ∃ k : ℕ, (k : ℤ) = (C.chainW p X N).NR := ⟨(C.chainW p X N).NR.toNat, by omega⟩
  have hgeo := sq_sum_geom_le ψ r hr0 hr1 n1n
    (fun n hn0 hn1 => (hgr n hn0 (by omega)).1.le)
    (fun n hn0 hn1 => by
      have h1 := (hgr n hn0 (by omega)).2
      have hγ' : 1 + C.nu1 / (C.CA + 1) = 1 + γ := rfl
      rw [hγ'] at h1
      rw [hr, ← div_eq_inv_mul, le_div_iff₀ (by linarith)]
      linarith)
  rw [hn1n] at hgeo
  -- the value at the row `n_1 + 1`
  have hsuccu := uNode_succ_sub' (Fz.step N) (C.chainW p X N).NR
  have hZn : C.Zof p X N ((C.chainW p X N).NR + 1) ≤ 0 :=
    Zof_nonpos_of_le C hp hX hN hs2 hVpre (k := (C.chainW p X N).NR + 1) (by omega) (by linarith)
  have hbound := HE p hp N hN (hs0b) X hX ψ hJ hseed ((C.chainW p X N).NR + 1) (mem_Icc.mpr ⟨by omega, hn1NR⟩)
    (by linarith) (by linarith) hZn
  have hEsm := Eminus_left_small C hp hX hN hs2 hVpre (j := (C.chainW p X N).NR + 1) (by linarith) (by linarith)
  have hκ := kappaBal_pos (C.aOf p X N)
  set T0 : ℝ := |C.lamL p X N| / kappaBal (C.aOf p X N) with hT0
  have hT00 : 0 ≤ T0 := div_nonneg (abs_nonneg _) hκ.le
  have hψn1 : |ψ ((C.chainW p X N).NR + 1)| ≤ CE * T0 * Real.exp (-(softCQ C / Fz.step N)) := by
    refine hbound.trans ?_
    have hM1 := Mbal_le_one (C.aOf p X N) (C.Zof p X N ((C.chainW p X N).NR + 1))
    have hE0 := (Eminus_pos (C.aOf p X N) (C.Zof p X N ((C.chainW p X N).NR + 1))).le
    calc CE * T0 * (Eminus (C.aOf p X N) (C.Zof p X N ((C.chainW p X N).NR + 1)) * Mbal (C.aOf p X N) (C.Zof p X N ((C.chainW p X N).NR + 1)))
        ≤ CE * T0 * (Real.exp (-(softCQ C / Fz.step N)) * 1) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCE hT00)
          exact mul_le_mul hEsm hM1 (Mbal_pos _ _).le (Real.exp_pos _).le
      _ = _ := by ring
  have hψn1sq : ψ ((C.chainW p X N).NR + 1) ^ 2 ≤ (CE * T0) ^ 2 * Real.exp (-((2 * softCQ C) / Fz.step N)) := by
    have h1 : ψ ((C.chainW p X N).NR + 1) ^ 2 = |ψ ((C.chainW p X N).NR + 1)| ^ 2 := (sq_abs _).symm
    rw [h1]
    calc |ψ ((C.chainW p X N).NR + 1)| ^ 2 ≤ (CE * T0 * Real.exp (-(softCQ C / Fz.step N))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hψn1 2
      _ = (CE * T0) ^ 2 * (Real.exp (-(softCQ C / Fz.step N)) * Real.exp (-(softCQ C / Fz.step N))) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  calc ∑ n ∈ Finset.Icc (0 : ℤ) (C.chainW p X N).NR, softEnvWeb C p X N n ^ 2
      ≤ ∑ n ∈ Finset.Icc (0 : ℤ) (C.chainW p X N).NR, ((2 / C.c3W) * ψ n) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact pow_le_pow_left₀ (softEnvWeb_nonneg C p X N n) (hlow n hn) 2
    _ = (2 / C.c3W) ^ 2 * ∑ n ∈ Finset.Icc (0 : ℤ) (C.chainW p X N).NR, ψ n ^ 2 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; ring
    _ ≤ (2 / C.c3W) ^ 2 * (ψ ((C.chainW p X N).NR + 1) ^ 2 * Kr) := mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ ≤ (2 / C.c3W) ^ 2 * (((CE * T0) ^ 2 * Real.exp (-((2 * softCQ C) / Fz.step N))) * Kr) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hψn1sq hKr0
    _ = (2 / C.c3W) ^ 2 * Kr * CE ^ 2 * T0 ^ 2 * Real.exp (-((2 * softCQ C) / Fz.step N)) := by ring

end Left

/-! ### T2: the right Weber tail (iii), the mirror of T1 -/

section Right

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  {CL : SoftEdgeChart Fz P m q U V Lm} {CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm}

/-- Transport of a finite sum along `n ↦ N - n`: the rows `N - NR ≤ n ≤ N` against the rows `0 ≤ k ≤ NR`. -/
lemma sum_Icc_reflect (N NR : ℤ) (f : ℤ → ℝ) :
    ∑ n ∈ Finset.Icc (N - NR) N, f (N - n) = ∑ k ∈ Finset.Icc (0 : ℤ) NR, f k := by
  apply Finset.sum_nbij' (fun n => N - n) (fun k => N - k)
  · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro n _; simp
  · intro k _; simp
  · intro n _; rfl

/-- **T2: the right Weber tail** (`app_thmA` Step 4 (d) (iii)).  Apply `weber_tail` to the mirror chart `CR` (its row `k` is the left row `N - k`,
`uNode_mirror`, `aOf_mirror`), transport the sum along `n ↦ N - n`, and weight by `|kappa-hat|` with the premise
`|kappa-hat lam_R| <= C_k |lam_L|` (Step 4 (b), an explicit premise as in `SoftQuant.lean`).  The sites are the right Weber rows
`{n : u_n >= u_c + eta/2}`, i.e. `N - NR <= n <= N` for the last mirror Weber row `NR = CR.chainW.NR` (`shapeW` of `CR`). -/
theorem weber_tail_right (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC)
    (hm : 1 ≤ m) (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) :
    ∃ Cw cw h0 : ℝ, 0 < h0 ∧ 0 < cw ∧ ∀ p ∈ P, ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      ∀ Ck : ℝ, ∀ ψ : ℤ → ℝ, JacSol (mirrorFamily Fz) p N X (CR.chain p X N).NR ψ → ψ 0 = CR.psiHatL p X N 0 →
        |softKappa CL CR p X N * CR.lamL p X N| ≤ Ck * |CL.lamL p X N| →
        ∑ n ∈ (rowsOf N).filter (fun n => CL.uc p + CL.η / 2 ≤ uNode (Fz.step N) n),
            (|softKappa CL CR p X N| * softEnvWeb CR p X N ((N : ℤ) - n)) ^ 2 ≤
          Cw * Ck ^ 2 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Real.exp (-(cw / Fz.step N)) := by
  obtain ⟨Cw, cw, h0, h0pos, hcw, H⟩ := weber_tail CR hf hm hLm
  refine ⟨max Cw 0, cw, h0, h0pos, hcw, ?_⟩
  intro p hp N hN hstep X hX Ck ψ hJ hseed hk
  have hN0 : CR.N0 = CL.N0 := hM.2.2.2.2.2
  have hδ : CR.δ0 = CL.δ0 := hM.2.2.2.2.1
  have hηe : CR.η = CL.η := hM.2.2.2.1
  have huc : CR.uc p = Fz.L - CL.uc p := hM.1 p hp
  have hX' : |X - (mirrorFamily Fz).bandHi p| ≤ CR.δ0 := by
    rw [bandHi_mirror, hδ]; exact hX
  have hH : ∑ n ∈ Finset.Icc (0 : ℤ) (CR.chainW p X N).NR, softEnvWeb CR p X N n ^ 2 ≤
      Cw * (|CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Real.exp (-(cw / Fz.step N)) := by
    have h := H p hp N (by rw [hN0]; exact hN) hstep X hX' ψ hJ hseed
    rw [aOf_mirror hM hp X N] at h
    exact h
  have hsh := CR.shapeW p hp X hX' N (by rw [hN0]; exact hN)
  obtain ⟨-, -, hNR0, hA, hB⟩ := hsh
  have hL := step_mul_succ Fz N
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hmono : ∀ a b : ℤ, a ≤ b → uNode (Fz.step N) a ≤ uNode (Fz.step N) b :=
    fun a b hab => SoftEdgeChart.uNode_mono_le hh0.le hab
  have hA' : uNode (Fz.step N) (CR.chainW p X N).NR ≤ Fz.L - CL.uc p - CL.η / 2 := by
    have h := hA; rw [huc, hηe] at h; exact h
  have hB' : Fz.L - CL.uc p - CL.η / 2 < uNode (Fz.step N) ((CR.chainW p X N).NR + 1) := by
    have h := hB; rw [huc, hηe] at h; exact h
  have hucp := (CL.uc_spec p hp).1
  have hηp := CL.consts_pos.2.1
  -- the mirror identity `u_{N-k} = L - u_k`
  have hrefl : ∀ k : ℤ, uNode (Fz.step N) ((N : ℤ) - k) = Fz.L - uNode (Fz.step N) k :=
    fun k => uNode_mirror Fz.L (Fz.step N) N k hL
  set NR : ℤ := (CR.chainW p X N).NR with hNRdef
  have hNRN : NR ≤ (N : ℤ) := by
    have h1 := hA'
    have h2 : (NR : ℝ) < (N : ℝ) + 1 := by
      unfold uNode at h1
      have hlt : ((NR : ℝ) + 1 / 2) * Fz.step N < ((N : ℝ) + 1) * Fz.step N := by
        have : ((N : ℝ) + 1) * Fz.step N = Fz.L := by linarith [hL]
        nlinarith
      have := lt_of_mul_lt_mul_right hlt hh0.le
      linarith
    have h3 : NR < (N : ℤ) + 1 := by exact_mod_cast h2
    omega
  have hset : (rowsOf N).filter (fun n => CL.uc p + CL.η / 2 ≤ uNode (Fz.step N) n) =
      Finset.Icc ((N : ℤ) - NR) N := by
    ext n
    simp only [rowsOf, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h0n, hnN⟩, hu⟩
      by_contra hlt
      have h4 := hmono n ((N : ℤ) - (NR + 1)) (by omega)
      rw [hrefl (NR + 1)] at h4
      linarith
    · rintro ⟨h1, h2⟩
      refine ⟨⟨by omega, h2⟩, ?_⟩
      have h4 := hmono ((N : ℤ) - NR) n h1
      rw [hrefl NR] at h4
      linarith
  have e1 : ∑ n ∈ Finset.Icc ((N : ℤ) - NR) N, (|softKappa CL CR p X N| * softEnvWeb CR p X N ((N : ℤ) - n)) ^ 2 =
      |softKappa CL CR p X N| ^ 2 * ∑ k ∈ Finset.Icc (0 : ℤ) NR, softEnvWeb CR p X N k ^ 2 := by
    calc ∑ n ∈ Finset.Icc ((N : ℤ) - NR) N, (|softKappa CL CR p X N| * softEnvWeb CR p X N ((N : ℤ) - n)) ^ 2
        = ∑ n ∈ Finset.Icc ((N : ℤ) - NR) N,
            (fun k => |softKappa CL CR p X N| ^ 2 * softEnvWeb CR p X N k ^ 2) ((N : ℤ) - n) :=
          Finset.sum_congr rfl (fun n _ => by dsimp only; ring)
      _ = ∑ k ∈ Finset.Icc (0 : ℤ) NR, (fun k => |softKappa CL CR p X N| ^ 2 * softEnvWeb CR p X N k ^ 2) k :=
          sum_Icc_reflect (N : ℤ) NR (fun k => |softKappa CL CR p X N| ^ 2 * softEnvWeb CR p X N k ^ 2)
      _ = _ := by rw [Finset.mul_sum]
  rw [hset, e1]
  have hE : 0 ≤ Real.exp (-(cw / Fz.step N)) := (Real.exp_pos _).le
  have hkb := kappaBal_pos (CL.aOf p X N)
  have hm0 : 0 ≤ max Cw 0 := le_max_right _ _
  have h1 : |softKappa CL CR p X N| ^ 2 * ∑ k ∈ Finset.Icc (0 : ℤ) NR, softEnvWeb CR p X N k ^ 2 ≤
      |softKappa CL CR p X N| ^ 2 *
        (Cw * (|CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Real.exp (-(cw / Fz.step N))) :=
    mul_le_mul_of_nonneg_left hH (sq_nonneg _)
  have h2 : |softKappa CL CR p X N| ^ 2 *
        (Cw * (|CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Real.exp (-(cw / Fz.step N))) ≤
      max Cw 0 * (|softKappa CL CR p X N * CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 *
        Real.exp (-(cw / Fz.step N)) := by
    have hid : |softKappa CL CR p X N| ^ 2 * (|CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 =
        (|softKappa CL CR p X N * CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 := by
      rw [abs_mul]; ring
    calc |softKappa CL CR p X N| ^ 2 *
          (Cw * (|CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Real.exp (-(cw / Fz.step N)))
        = Cw * (|softKappa CL CR p X N| ^ 2 * (|CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2) *
            Real.exp (-(cw / Fz.step N)) := by ring
      _ = Cw * (|softKappa CL CR p X N * CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 *
            Real.exp (-(cw / Fz.step N)) := by rw [hid]
      _ ≤ max Cw 0 * (|softKappa CL CR p X N * CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 *
            Real.exp (-(cw / Fz.step N)) := by
          apply mul_le_mul_of_nonneg_right _ hE
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  have h3 : (|softKappa CL CR p X N * CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 ≤
      Ck ^ 2 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 := by
    have hc0 : 0 ≤ |softKappa CL CR p X N * CR.lamL p X N| / kappaBal (CL.aOf p X N) := by positivity
    have hc : |softKappa CL CR p X N * CR.lamL p X N| / kappaBal (CL.aOf p X N) ≤
        Ck * |CL.lamL p X N| / kappaBal (CL.aOf p X N) := div_le_div_of_nonneg_right hk hkb.le
    calc (|softKappa CL CR p X N * CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2
        ≤ (Ck * |CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 := pow_le_pow_left₀ hc0 hc 2
      _ = Ck ^ 2 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 := by ring
  have h4 : max Cw 0 * (|softKappa CL CR p X N * CR.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 *
        Real.exp (-(cw / Fz.step N)) ≤
      max Cw 0 * (Ck ^ 2 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2) *
        Real.exp (-(cw / Fz.step N)) := by
    apply mul_le_mul_of_nonneg_right _ hE
    exact mul_le_mul_of_nonneg_left h3 hm0
  have h5 : max Cw 0 * (Ck ^ 2 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2) *
      Real.exp (-(cw / Fz.step N)) = max Cw 0 * Ck ^ 2 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 *
      Real.exp (-(cw / Fz.step N)) := by ring
  linarith [h1, h2, h4, h5]

end Right

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.weber_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms weber_tail

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.sq_sum_geom_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sq_sum_geom_le

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.geom_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms geom_up

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.geom_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms geom_down

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.weber_tail_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms weber_tail_right

end FormalResearch.JacobiEigenvectors.TheoremA

end
