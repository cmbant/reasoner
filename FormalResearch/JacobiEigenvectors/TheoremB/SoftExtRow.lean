module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.Collar
public import FormalResearch.JacobiEigenvectors.TheoremB.SoftOneStep
public import FormalResearch.JacobiEigenvectors.TheoremB.BulkOneStep2

/-!
# Paper J, Theorem B, L3.5b (soft halves), part 4: the exterior row (I3) of the soft charts

Source: Paper J `app_thmB.tex`, "(I3): exterior rows" (soft half-collar: the exterior row `n_L - 1` resp. `n_R + 1` lies in the forbidden region, `E` is exponentially small) and the proof of `lem:tha-collar` (1).

## Proved here

* `pc_ext_y`: for a row `j` of patch 2 with `-2 eta <= x_j <= -5 eta/16`, the first component of the model pair, `y_j = wf 2 0 .. 0 = kappa_b U(a, -Z_j)`, is `<= C_PC e^{-c_Q/h}` (the companion `pc_ext_row` has the second component and `phi`).
* `soft_ext_cols`: the exterior-row entries of the soft charts, `|sigma^{[m+1]}_k| |y_{ext,k}|`, are `<= D e^{-c/h}`: left half `sigma = lambda_L/(kappa_b hat N)` (order `m+1`), `y_ext` at the chain row `n_L - 1 = floor((u_c - eta/2)/h - 1/2)` of the order-`m` chain;
  right half `sigma = hat kappa lambda_R/(kappa_b hat N)` and `y_ext` at the mirror row `N - ceil((u_c + eta/2)/h - 1/2)`.  With `|sigma| <= C/sqrt(c_n)` (`soft_norm_lb`, `soft_kappa_bound`) and `|y_ext| <= C_PC e^{-c/h}`.
* `soft_ext_row_l2`: the `l^2` norm over `<= N + 1 = L/h` columns of such entries (the exterior row of a left resp. right half, `1 * sigma * y_ext`) is `<= 1` for `h <= h_1` (`(I3)`, with `C_E >= 1`; `ext_small`, `l2_card_le`).

## Differences from the paper

The paper bounds `|sigma| |phi|` and `|sigma| |scaled derivative|` (`lem:tha-collar` (1)); the model value `y = kappa_b U(a,-Z)` of the chart is bounded directly by the same envelope (`pcMinus0_env`), which avoids inverting `phi = A y + h B y~`.

## Not formalised here

The instantiation at `softJBChart` (the exterior row of the chart is `chartExtRowDn`, equal to the rows `j` above once `lo = floor((u_c - eta/2)/h - 1/2) + 1` resp. `lo + R = ceil((u_c + eta/2)/h - 1/2)`), and the hypothesis `a <= 1` of the soft columns (assembly).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section Row

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- **the model value `y` at an exterior row is exponentially small**: `|wf 2 0 .. 0| = |kappa_b U(a, -Z_j)| <= C_PC e^{-c_Q/h}` (see `pc_ext_row`). -/
theorem pc_ext_y {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N) (hh : Fz.step N ≤ min (winH1 C) (min C.softH2 1)) {j : ℤ}
    (hj0 : 0 ≤ j) (hjN : j ≤ N) (hj1 : (C.chain p X N).jj 1 ≤ j) (hj2 : j ≤ (C.chain p X N).NR)
    (hlo : -(2 * C.η) ≤ uNode (Fz.step N) j - C.uc p) (hhi : uNode (Fz.step N) j - C.uc p ≤ -(5 * C.η / 16)) :
    |(C.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 0| ≤ CPC * Real.exp (-(softCQ C / Fz.step N)) := by
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs1 : Fz.step N ≤ winH1 C := hh.trans (min_le_left _ _)
  have hs2 : Fz.step N ≤ C.softH2 := (hh.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hη := C.consts_pos.2.1
  have hCPC : 0 ≤ CPC := le_trans hf.cPC_pos.le hf.cPC_le
  have hjr : j ∈ rowsOf N := by unfold rowsOf; exact Finset.mem_Icc.mpr ⟨hj0, hjN⟩
  have hZ : C.Zof p X N j ≤ 0 := Zof_nonpos_of_near C hp hX hjr (by linarith)
  have hj2' : j ≤ (C.chain p X N).NR + 1 := by omega
  obtain ⟨e1, -⟩ := pcMinus0_env hf (C.aOf p X N) (C.Zof p X N j) hZ
  obtain ⟨lam, hV⟩ : ∃ lam, ((C.chain p X N).rescale1 lam).PreValid C.cs (Fz.step N) m := ⟨_, C.valid p hp X hX N hN⟩
  have hE := Eminus_left_small C hp hX hN hs2 hV hlo hhi
  have hEp := Eminus_pos (C.aOf p X N) (C.Zof p X N j)
  have hM1 := Mbal_le_one (C.aOf p X N) (C.Zof p X N j)
  have hM0 := Mbal_pos (C.aOf p X N) (C.Zof p X N j)
  have hw := C.wf2_eq p hp X hX N hN j (Finset.mem_Icc.mpr ⟨hj1, hj2'⟩) 0
  have h0 : (C.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 0 =
      kappaBal (C.aOf p X N) * U (C.aOf p X N) (-(C.Zof p X N j)) := by
    rw [hw]
    simp [wm_pcMinus0, SoftEdgeChart.aOf, SoftEdgeChart.Zof]
  rw [h0]
  calc |kappaBal (C.aOf p X N) * U (C.aOf p X N) (-(C.Zof p X N j))|
      ≤ CPC * Eminus (C.aOf p X N) (C.Zof p X N j) * Mbal (C.aOf p X N) (C.Zof p X N j) := e1
    _ ≤ CPC * Eminus (C.aOf p X N) (C.Zof p X N j) * 1 := by gcongr
    _ ≤ CPC * Real.exp (-(softCQ C / Fz.step N)) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left hE hCPC

end Row

section Cols

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}

/-- **The exterior-row entries of the soft charts are exponentially small**: see the module docstring. -/
theorem soft_ext_cols {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC)
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1))
    (CL1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1)) (CR1 : SoftEdgeChart (mirrorFamily Fz) P (m + 1) q U V (fun _ => 1))
    (hM : SoftMirror CL CR) (hM1 : SoftMirror CL1 CR1) (hδ1 : CL1.δ0 = CL.δ0)
    (r : ℕ) (hr : StdAssump Fz P (q / 2) r) :
    ∃ D c h1 : ℝ, 0 ≤ D ∧ 0 < c ∧ 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CL1.N0 ≤ N → Fz.step N ≤ h1 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      CL1.aOf p X N ≤ 1 →
      |CL1.lamL p X N / (kappaBal (CL1.aOf p X N) * softNorm CL1 CR1 p X N)| *
          |(CL.chain p X N).wf 2 0 (uNode (Fz.step N) ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋) (Fz.step N) 0| ≤ D * Real.exp (-c / Fz.step N) ∧
      |softKappa CL1 CR1 p X N * CR1.lamL p X N / (kappaBal (CR1.aOf p X N) * softNorm CL1 CR1 p X N)| *
          |(CR.chain p X N).wf 2 0 (uNode (Fz.step N) ((N : ℤ) - ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉)) (Fz.step N) 0|
        ≤ D * Real.exp (-c / Fz.step N) := by
  obtain ⟨cn, hn0, hcn, hn0p, Hn⟩ := soft_norm_lb CL1 CR1 hf r hr
  obtain ⟨Ck, hk0, hCk, hk0p, Hk⟩ := soft_kappa_bound CL1 CR1 hM1 hf
  have hCPC : 0 ≤ CPC := le_trans hf.cPC_pos.le hf.cPC_le
  have hcQL := softCQ_pos CL
  have hcQR := softCQ_pos CR
  have hηe : CR.η = CL.η := hM.2.2.2.1
  have hδ : CR.δ0 = CL.δ0 := hM.2.2.2.2.1
  have hN0 : CR.N0 = CL.N0 := hM.2.2.2.2.2
  have hη := CL.consts_pos.2.1
  have hsq : 0 < Real.sqrt cn := Real.sqrt_pos.mpr hcn
  refine ⟨(1 + Ck) / Real.sqrt cn * CPC, min (softCQ CL) (softCQ CR),
    min hn0 (min hk0 (min (CL.η / 2) (min (winH1 CL) (min (winH1 CR) (min CL.softH2 (min CR.softH2 1)))))),
    by positivity, lt_min hcQL hcQR,
    lt_min hn0p (lt_min hk0p (lt_min (by linarith) (lt_min (winH1_pos CL) (lt_min (winH1_pos CR)
      (lt_min CL.softH2_pos (lt_min CR.softH2_pos one_pos)))))), ?_⟩
  intro p hp N hN hstep X hX ha
  simp only [le_min_iff] at hstep
  obtain ⟨s1, s2, s3, s4, s5, s6, s6', s7⟩ := hstep
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hN1' : CL1.N0 ≤ N := (le_max_right _ _).trans hN
  have hN2 : CR.N0 ≤ N := by rw [hN0]; exact hN1
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hX1 : |X - Fz.bandHi p| ≤ CL1.δ0 := by rw [hδ1]; exact hX
  have hκ := kappaBal_pos (CL1.aOf p X N)
  have hSnn : 0 ≤ softNorm CL1 CR1 p X N := by unfold softNorm glueNorm; exact Real.sqrt_nonneg _
  have hT0 : 0 ≤ |CL1.lamL p X N| / kappaBal (CL1.aOf p X N) := by positivity
  have hone : 1 ≤ Fz.step N ^ (-(1 : ℝ) / 2) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh0 s7 (by norm_num)
  have hnorm : cn * (|CL1.lamL p X N| / kappaBal (CL1.aOf p X N)) ^ 2 ≤ softNorm CL1 CR1 p X N ^ 2 := by
    have h1 := Hn p hp N hN1' s1 X hX1 ha
    have hT2 := sq_nonneg (|CL1.lamL p X N| / kappaBal (CL1.aOf p X N))
    calc cn * (|CL1.lamL p X N| / kappaBal (CL1.aOf p X N)) ^ 2
        = cn * ((|CL1.lamL p X N| / kappaBal (CL1.aOf p X N)) ^ 2 * 1) := by ring
      _ ≤ cn * ((|CL1.lamL p X N| / kappaBal (CL1.aOf p X N)) ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hone hT2) hcn.le
      _ ≤ _ := h1
  have hratio := ratio_le _ _ cn hcn hT0 hSnn hnorm
  have hσL : |CL1.lamL p X N / (kappaBal (CL1.aOf p X N) * softNorm CL1 CR1 p X N)| ≤ 1 / Real.sqrt cn := by
    rw [abs_div, abs_mul, abs_of_pos hκ, abs_of_nonneg hSnn, ← div_div]
    exact hratio
  have hkb := Hk p hp N hN1' s2 X hX1 ha
  have hκR : kappaBal (CR1.aOf p X N) = kappaBal (CL1.aOf p X N) := by rw [aOf_mirror hM1 hp X N]
  have hσR : |softKappa CL1 CR1 p X N * CR1.lamL p X N / (kappaBal (CR1.aOf p X N) * softNorm CL1 CR1 p X N)| ≤ Ck / Real.sqrt cn := by
    rw [abs_div, abs_mul (kappaBal _), hκR, abs_of_pos hκ, abs_of_nonneg hSnn]
    calc |softKappa CL1 CR1 p X N * CR1.lamL p X N| / (kappaBal (CL1.aOf p X N) * softNorm CL1 CR1 p X N)
        ≤ Ck * |CL1.lamL p X N| / (kappaBal (CL1.aOf p X N) * softNorm CL1 CR1 p X N) :=
          div_le_div_of_nonneg_right hkb (by positivity)
      _ = Ck * (|CL1.lamL p X N| / kappaBal (CL1.aOf p X N) / softNorm CL1 CR1 p X N) := by
          rw [div_div, mul_div_assoc]
      _ ≤ Ck * (1 / Real.sqrt cn) := mul_le_mul_of_nonneg_left hratio hCk
      _ = Ck / Real.sqrt cn := by ring
  have hhL : Fz.step N ≤ min (winH1 CL) (min CL.softH2 1) := le_min s4 (le_min s6 s7)
  have hhR : Fz.step N ≤ min (winH1 CR) (min CR.softH2 1) := le_min s5 (le_min s6' s7)
  have hexpL : Real.exp (-(softCQ CL / Fz.step N)) ≤ Real.exp (-(min (softCQ CL) (softCQ CR)) / Fz.step N) := by
    have := exp_mono_c (softCQ CL) (min (softCQ CL) (softCQ CR)) (Fz.step N) hh0 (min_le_left _ _)
    rwa [show -(softCQ CL / Fz.step N) = -softCQ CL / Fz.step N by ring]
  have hexpR : Real.exp (-(softCQ CR / Fz.step N)) ≤ Real.exp (-(min (softCQ CL) (softCQ CR)) / Fz.step N) := by
    have := exp_mono_c (softCQ CR) (min (softCQ CL) (softCQ CR)) (Fz.step N) hh0 (min_le_right _ _)
    rwa [show -(softCQ CR / Fz.step N) = -softCQ CR / Fz.step N by ring]
  have hex0 := Real.exp_pos (-(min (softCQ CL) (softCQ CR)) / Fz.step N)
  constructor
  · obtain ⟨jL0, jLN, jL1, jLR, jLlo, jLhi⟩ := ext_left_row CL hp hX hN1 (by linarith) (j := ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋) rfl
    have hy := pc_ext_y CL hf hp hX hN1 hhL jL0 jLN jL1 jLR jLlo jLhi
    calc _ ≤ (1 / Real.sqrt cn) * (CPC * Real.exp (-(softCQ CL / Fz.step N))) := mul_le_mul hσL hy (abs_nonneg _) (by positivity)
      _ ≤ (1 / Real.sqrt cn) * (CPC * Real.exp (-(min (softCQ CL) (softCQ CR)) / Fz.step N)) := by
          gcongr
      _ ≤ (1 + Ck) / Real.sqrt cn * CPC * Real.exp (-(min (softCQ CL) (softCQ CR)) / Fz.step N) := by
          have : 0 ≤ CPC * Real.exp (-(min (softCQ CL) (softCQ CR)) / Fz.step N) := by positivity
          calc (1 / Real.sqrt cn) * (CPC * Real.exp (-(min (softCQ CL) (softCQ CR)) / Fz.step N))
              ≤ ((1 + Ck) / Real.sqrt cn) * (CPC * Real.exp (-(min (softCQ CL) (softCQ CR)) / Fz.step N)) := by
                apply mul_le_mul_of_nonneg_right _ this
                exact div_le_div_of_nonneg_right (by linarith) hsq.le
            _ = _ := by ring
  · have hX' : |X - (mirrorFamily Fz).bandHi p| ≤ CR.δ0 := by rw [bandHi_mirror, hδ]; exact hX
    have hL := step_mul_succ Fz N
    have huc : CR.uc p = Fz.L - CL.uc p := hM.1 p hp
    have hjR : (N : ℤ) - ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉ =
        ⌊(CR.uc p - CR.η / 2) / (mirrorFamily Fz).step N - 1 / 2⌋ := by
      rw [floor_mirror N (Fz.step N) (CL.uc p) CL.η Fz.L hh0 hL, huc, hηe]
      rfl
    obtain ⟨jR0, jRN, jR1, jRR, jRlo, jRhi⟩ := ext_left_row CR hp hX' hN2 (by show Fz.step N ≤ CR.η / 2; rw [hηe]; exact s3)
      (j := (N : ℤ) - ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉) hjR
    have hy := pc_ext_y CR hf hp hX' hN2 hhR jR0 jRN jR1 jRR jRlo jRhi
    calc _ ≤ (Ck / Real.sqrt cn) * (CPC * Real.exp (-(softCQ CR / Fz.step N))) := mul_le_mul hσR hy (abs_nonneg _) (by positivity)
      _ ≤ (Ck / Real.sqrt cn) * (CPC * Real.exp (-(min (softCQ CL) (softCQ CR)) / Fz.step N)) := by
          gcongr
      _ ≤ (1 + Ck) / Real.sqrt cn * CPC * Real.exp (-(min (softCQ CL) (softCQ CR)) / Fz.step N) := by
          have : 0 ≤ CPC * Real.exp (-(min (softCQ CL) (softCQ CR)) / Fz.step N) := by positivity
          calc (Ck / Real.sqrt cn) * (CPC * Real.exp (-(min (softCQ CL) (softCQ CR)) / Fz.step N))
              ≤ ((1 + Ck) / Real.sqrt cn) * (CPC * Real.exp (-(min (softCQ CL) (softCQ CR)) / Fz.step N)) := by
                apply mul_le_mul_of_nonneg_right _ this
                exact div_le_div_of_nonneg_right (by linarith) hsq.le
            _ = _ := by ring

end Cols

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_ext_cols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_ext_cols

section L2

/-- `sqrt(L/h) A e^{-c/h} <= 1` for `h` small. -/
theorem ext_small {L A c : ℝ} (hL : 0 < L) (hA : 0 ≤ A) (hc : 0 < c) :
    ∃ h1 : ℝ, 0 < h1 ∧ ∀ h : ℝ, 0 < h → h ≤ h1 → Real.sqrt (L / h) * (A * Real.exp (-c / h)) ≤ 1 := by
  obtain ⟨x₀, hx₀⟩ := FormalResearch.JB.eventually_small_tail 1 c ((L + 1) * A) hc
  set X : ℝ := max x₀ 1 with hX
  have hX1 : 1 ≤ X := le_max_right _ _
  have hX0 : 0 < X := by linarith
  refine ⟨1 / X, by positivity, fun h hh hh1 => ?_⟩
  set x : ℝ := 1 / h with hx
  have hx0 : 0 < x := by positivity
  have hxX : X ≤ x := by
    rw [hx, le_div_iff₀ hh]
    have := (le_div_iff₀ hX0).1 hh1
    linarith
  have hx1 : 1 ≤ x := hX1.trans hxX
  have key := hx₀ x ((le_max_left _ _).trans hxX) hx0
  have e2 : -c / h = -c * x := by rw [hx]; field_simp
  have e1 : L / h = L * x := by rw [hx]; field_simp
  rw [e2, e1]
  have hsq : Real.sqrt (L * x) ≤ (L + 1) * x := by
    have hz : 0 ≤ L * x := by positivity
    have h1 : Real.sqrt (L * x) ≤ L * x + 1 := by
      have := Real.sqrt_le_sqrt (show L * x ≤ (L * x + 1) ^ 2 by nlinarith)
      rwa [Real.sqrt_sq (by linarith)] at this
    nlinarith
  have hpos : 0 ≤ A * Real.exp (-c * x) := by positivity
  calc Real.sqrt (L * x) * (A * Real.exp (-c * x)) ≤ ((L + 1) * x) * (A * Real.exp (-c * x)) :=
        mul_le_mul_of_nonneg_right hsq hpos
    _ = (L + 1) * A * (x ^ 1 * Real.exp (-c * x)) := by ring
    _ ≤ 1 := key

/-- the `l^2` norm over at most `N + 1 = L/h` entries each `<= B` is `<= sqrt(L/h) B`. -/
theorem l2_card_le {N : ℕ} {L h B : ℝ} (hh : 0 < h) (hL : h * ((N : ℝ) + 1) = L) (hB : 0 ≤ B) (cols : Finset (Fin (N + 1))) (v : cols → ℝ)
    (hv : ∀ k, |v k| ≤ B) : FormalResearch.JB.jbL2 Finset.univ v ≤ Real.sqrt (L / h) * B := by
  refine (jbL2_le_sqrt_card_mul Finset.univ v hB (fun k _ => hv k)).trans ?_
  refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) hB
  rw [Finset.card_univ, Fintype.card_coe]
  have : L / h = (N : ℝ) + 1 := by rw [← hL]; field_simp
  rw [this]
  have : cols.card ≤ N + 1 := by
    calc cols.card ≤ (Finset.univ : Finset (Fin (N + 1))).card := Finset.card_le_univ _
      _ = N + 1 := by simp
  exact_mod_cast this

end L2

section Cols2

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}

/-- **(I3) for the soft halves**: the exterior row `(omega sigma^{[m+1]} y_ext)_k` of the left half (exterior chain row `j = n_L - 1 = floor((u_c - eta/2)/h - 1/2)`, order-`m` chain `CL`, `sigma = lambda_L/(kappa_b hat N)` of order `m+1`) and of the
right half (mirror chain row `j = N - ceil((u_c + eta/2)/h - 1/2)`, `sigma = hat kappa lambda_R/(kappa_b hat N)`) has `l^2` norm `<= 1` over any set of columns with energies near the edge and `a <= 1`, for `h <= h_1`
(`h_1` independent of `p, N`, the columns).  (`C_E >= 1` then covers `JB.Chart.Ok.ext_row`.) -/
theorem soft_ext_row_l2 {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC)
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1))
    (CL1 : SoftEdgeChart Fz P (m + 1) q U V (fun _ => 1)) (CR1 : SoftEdgeChart (mirrorFamily Fz) P (m + 1) q U V (fun _ => 1))
    (hM : SoftMirror CL CR) (hM1 : SoftMirror CL1 CR1) (hδ1 : CL1.δ0 = CL.δ0)
    (r : ℕ) (hr : StdAssump Fz P (q / 2) r) :
    ∃ h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CL1.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ (Xc : Fin (N + 1) → ℝ) (cols : Finset (Fin (N + 1))), (∀ k : cols, |Xc k - Fz.bandHi p| ≤ CL.δ0) → (∀ k : cols, CL1.aOf p (Xc k) N ≤ 1) →
      (∀ j : ℤ, j = ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋ →
        FormalResearch.JB.jbL2 Finset.univ (fun k : cols => 1 * (CL1.lamL p (Xc k) N / (kappaBal (CL1.aOf p (Xc k) N) * softNorm CL1 CR1 p (Xc k) N)) *
          (CL.chain p (Xc k) N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 0) ≤ 1) ∧
      (∀ j : ℤ, j = (N : ℤ) - ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉ →
        FormalResearch.JB.jbL2 Finset.univ (fun k : cols => 1 *
          (softKappa CL1 CR1 p (Xc k) N * CR1.lamL p (Xc k) N / (kappaBal (CR1.aOf p (Xc k) N) * softNorm CL1 CR1 p (Xc k) N)) *
          (CR.chain p (Xc k) N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 0) ≤ 1) := by
  obtain ⟨D, c, h1, hD, hc, hh1, H⟩ := soft_ext_cols hf CL CR CL1 CR1 hM hM1 hδ1 r hr
  obtain ⟨h2, hh2, H2⟩ := ext_small (L := Fz.L) (A := D) (c := c) Fz.L_pos hD hc
  refine ⟨min h1 h2, lt_min hh1 hh2, ?_⟩
  intro p hp N hN hstep Xc cols hX ha
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hL := step_mul_succ Fz N
  have hs1 : Fz.step N ≤ h1 := hstep.trans (min_le_left _ _)
  have hs2 : Fz.step N ≤ h2 := hstep.trans (min_le_right _ _)
  have hsm := H2 _ hh0 hs2
  constructor
  · intro j hj
    refine (l2_card_le hh0 hL (by positivity) cols _ (fun k => ?_)).trans hsm
    rw [one_mul, abs_mul]
    subst hj
    exact (H p hp N hN hs1 (Xc k) (hX k) (ha k)).1
  · intro j hj
    refine (l2_card_le hh0 hL (by positivity) cols _ (fun k => ?_)).trans hsm
    rw [one_mul, abs_mul]
    subst hj
    exact (H p hp N hN hs1 (Xc k) (hX k) (ha k)).2

end Cols2

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_ext_row_l2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_ext_row_l2

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.pc_ext_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_ext_y

end FormalResearch.JacobiEigenvectors.TheoremB

end
