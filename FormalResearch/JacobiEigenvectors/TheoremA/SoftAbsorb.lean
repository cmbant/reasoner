module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftTransfer

/-!
# Paper J, Layer 2 (L2.C6): the absorption of the connection term (R1), geometry of the overlap bonds

Source: Paper J `app_thmA.tex` "The soft edges: proof of Proposition prop:tha-W2", Step 3, last paragraph ("The second term in (tha-connect) is at most `Lambda lambda E_{j_1}^2 E_n^{-1} M_n` ...
its ratio to the error bound is `Lambda h^{-m} (E_{j_1}/E_n)^2 <= e^{-c eta^2/h}` for `u_n >= u_c - eta/2` ... Either way it is absorbed").

## Proved here

* `j2_ge`: the switch bond is near the fold, `x_{j_2} >= -eta/4` (`zeta_far`: `zeta` does not vanish on `eta/4 <= |x| <= 2 eta`, `d_+ h < sqrt(c_{z1})`).
* `Eminus_j1_decay` (**R1**): `E_-(Z_{j_1}) <= exp(-c_E/h) E_-(Z)` for every `Z` in `[zeta(-eta/2)/sqrt h, 0]` (so for every PC row `j_1 < k <= j_2` with `u_k > u_c - eta/2`), `c_E = sqrt(c_{z1}/8) d_- eta/2`;
  `Eminus_j1_small`: `E_-(Z_{j_1}) <= exp(-c_E/h)`.  Proof: `Eminus_decay` on `[Z_{j_1}, zeta(-eta/2)/sqrt h]` where `Z^2/4 + a >= c_{z1}/(8h)` (`Zq_lb`) and `zeta' >= d_-`.

## Not formalised

The comparison with the paper's exponent `c eta^2` (the constants differ; only `exp(-c/h)` with `c > 0` independent of `h` is used).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Engine

namespace SoftEdgeChart

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart F P m q U V Lm)

open SoftEdgeCore

/-- the smallness threshold of the absorption: `h <= h_1` and `d_+ h <= sqrt(c_{z1})/2`. -/
def softH2 : ℝ := min C.softH1 (Real.sqrt C.cz1 / (2 * C.dp))

lemma softH2_pos : 0 < C.softH2 := by
  obtain ⟨-, hη, hdm, hdmp, -⟩ := C.consts_pos
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hz := C.consts_pos2.2
  unfold softH2
  exact lt_min C.softH1_pos (by positivity)

lemma softH2_le_H1 : C.softH2 ≤ C.softH1 := min_le_left _ _

lemma softH2_le_dp : C.dp * C.softH2 ≤ Real.sqrt C.cz1 / 2 := by
  obtain ⟨-, hη, hdm, hdmp, -⟩ := C.consts_pos
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have h1 : C.softH2 ≤ Real.sqrt C.cz1 / (2 * C.dp) := min_le_right _ _
  rw [le_div_iff₀ (by positivity)] at h1
  linarith

/-- the exponent of the absorption: `c_E = sqrt(c_{z1}/8) d_- eta / 2`. -/
def cE : ℝ := Real.sqrt (C.cz1 / 8) * C.dm * C.η / 2

lemma cE_pos : 0 < C.cE := by
  obtain ⟨-, hη, hdm, -⟩ := C.consts_pos
  have hz := C.consts_pos2.2
  unfold cE
  have : 0 < Real.sqrt (C.cz1 / 8) := Real.sqrt_pos.mpr (by positivity)
  positivity

section Absorb

variable {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : |X - F.bandHi μ| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N)
  (hh : F.step N ≤ C.softH2) {lam : ℝ}
  (hV : ((C.chain μ X N).rescale1 lam).PreValid C.cs (F.step N) m)

include hμ hX hN hh hV

/-- **The switch bond is near the fold**: `x_{j_2} >= -eta/4` (the coordinate `zeta` cannot vanish at `|x| >= eta/4`). -/
lemma j2_ge :
    -(C.η / 4) ≤ uNode (F.step N) ((C.chain μ X N).jj 2) - C.uc μ := by
  have hhH1 : F.step N ≤ C.softH1 := hh.trans C.softH2_le_H1
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hμ hX hN hhH1 hV
  obtain ⟨-, hη, hdm, hdmp, -⟩ := C.consts_pos
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hh0 : 0 < F.step N := step_pos (F := F) N
  have hhη : F.step N ≤ C.η / 2 := hhH1.trans C.softH1_le_eta
  have hα := C.abs_alpha_le hX
  by_contra hcon
  have hlt : uNode (F.step N) ((C.chain μ X N).jj 2) - C.uc μ < -(C.η / 4) := not_le.mp hcon
  have hx2lo : -(2 * C.η) ≤ uNode (F.step N) ((C.chain μ X N).jj 2) - C.uc μ := by
    have : uNode (F.step N) ((C.chain μ X N).jj 1 + 1) ≤ uNode (F.step N) ((C.chain μ X N).jj 2) :=
      uNode_mono_le hh0.le (by omega)
    linarith
  have hx12 : uNode (F.step N) ((C.chain μ X N).jj 2 + 1) - C.uc μ - (uNode (F.step N) ((C.chain μ X N).jj 2) - C.uc μ) = F.step N := by
    unfold uNode; push_cast; ring
  have hmvt := C.zeta_mvt hμ hα hx2lo (by linarith) hx3
  rw [hx12] at hmvt
  have hfar := C.zeta_far μ hμ _ hα (uNode (F.step N) ((C.chain μ X N).jj 2) - C.uc μ)
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_of_neg (by linarith)]; linarith)
  have hz := C.consts_pos2.2
  have hzsq : C.cz1 ≤ C.zeta μ (F.bandHi μ - X) (uNode (F.step N) ((C.chain μ X N).jj 2) - C.uc μ) ^ 2 := by
    have : 0 ≤ max (C.muS 0 μ (F.bandHi μ - X)) 0 := le_max_right _ _
    linarith
  have hzneg : C.zeta μ (F.bandHi μ - X) (uNode (F.step N) ((C.chain μ X N).jj 2) - C.uc μ) ≤ -Real.sqrt C.cz1 := by
    have h1 : Real.sqrt C.cz1 ≤ |C.zeta μ (F.bandHi μ - X) (uNode (F.step N) ((C.chain μ X N).jj 2) - C.uc μ)| := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hzsq
    rw [abs_of_nonpos hza] at h1
    linarith
  have h2 := C.softH2_le_dp
  have hhH2 : C.dp * F.step N ≤ C.dp * C.softH2 := mul_le_mul_of_nonneg_left hh hdp.le
  have hsq : 0 < Real.sqrt C.cz1 := Real.sqrt_pos.mpr hz
  have hzb' : C.zeta μ (F.bandHi μ - X) (uNode (F.step N) ((C.chain μ X N).jj 2 + 1) - C.uc μ) ≤ 0 := by
    linarith [hmvt.2]
  linarith

/-- the intermediate point `hat Z = zeta(-eta/2)/sqrt h`. -/
def zhat (μ : Par) (X : ℝ) (N : ℕ) : ℝ := C.zeta μ (F.bandHi μ - X) (-(C.η / 2)) / Real.sqrt (F.step N)

/-- **Absorption (R1)**: for every `Z` with `hat Z <= Z <= 0`, `E_-(a, Z_{j_1}) <= exp(-c_E/h) E_-(a, Z)`. -/
lemma Eminus_j1_decay {z : ℝ} (hz1 : C.zhat μ X N ≤ z) (hz2 : z ≤ 0) :
    Eminus (C.aOf μ X N) (C.Zof μ X N ((C.chain μ X N).jj 1))
      ≤ Real.exp (-(C.cE / F.step N)) * Eminus (C.aOf μ X N) z := by
  have hhH1 : F.step N ≤ C.softH1 := hh.trans C.softH2_le_H1
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hμ hX hN hhH1 hV
  obtain ⟨-, hη, hdm, hdmp, -⟩ := C.consts_pos
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hh0 : 0 < F.step N := step_pos (F := F) N
  have hhη : F.step N ≤ C.η / 2 := hhH1.trans C.softH1_le_eta
  have hα := C.abs_alpha_le hX
  have hs : 0 < Real.sqrt (F.step N) := Real.sqrt_pos.mpr hh0
  have hs2 : Real.sqrt (F.step N) ^ 2 = F.step N := Real.sq_sqrt hh0.le
  have hz := C.consts_pos2.2
  -- the points
  have hx1lo : -(2 * C.η) ≤ uNode (F.step N) ((C.chain μ X N).jj 1) - C.uc μ := by
    have hx12 : uNode (F.step N) ((C.chain μ X N).jj 1 + 1) - C.uc μ - (uNode (F.step N) ((C.chain μ X N).jj 1) - C.uc μ) = F.step N := by
      unfold uNode; push_cast; ring
    linarith
  have hmvt := C.zeta_mvt hμ hα hx1lo (by linarith : uNode (F.step N) ((C.chain μ X N).jj 1) - C.uc μ ≤ -(C.η / 2))
    (by linarith : -(C.η / 2) ≤ 2 * C.η)
  have hlen : C.dm * (C.η / 2) ≤ C.zeta μ (F.bandHi μ - X) (-(C.η / 2))
      - C.zeta μ (F.bandHi μ - X) (uNode (F.step N) ((C.chain μ X N).jj 1) - C.uc μ) := by
    have h1 : C.dm * (C.η / 2) ≤ C.dm * (-(C.η / 2) - (uNode (F.step N) ((C.chain μ X N).jj 1) - C.uc μ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hdm.le
    linarith [hmvt.1]
  -- z1 <= zhat
  have hz1hat : C.Zof μ X N ((C.chain μ X N).jj 1) ≤ C.zhat μ X N := by
    rw [Zof_eq]; unfold zhat
    apply div_le_div_of_nonneg_right _ hs.le
    have : 0 ≤ C.dm * (C.η / 2) := by positivity
    linarith
  -- the margin at hat Z
  have hmar : (Real.sqrt (C.cz1 / 8) / Real.sqrt (F.step N)) ^ 2 ≤ C.zhat μ X N ^ 2 / 4 + C.aOf μ X N := by
    have hq := C.Zq_lb hμ hX hhH1 (x := -(C.η / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
      (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
    have e : C.zhat μ X N ^ 2 / 4 + C.aOf μ X N = (C.zeta μ (F.bandHi μ - X) (-(C.η / 2)) ^ 2 / 4 - C.muTilde μ X N) / F.step N := by
      unfold zhat; rw [aOf_eq, div_pow, hs2]; field_simp; ring
    rw [e, div_pow, Real.sq_sqrt (by positivity), hs2]
    exact div_le_div_of_nonneg_right hq hh0.le
  -- hat Z <= 0
  have hhat0 : C.zhat μ X N ≤ 0 := le_trans hz1 hz2
  have hdec := Eminus_decay (C.aOf μ X N) (Real.sqrt (C.cz1 / 8) / Real.sqrt (F.step N)) hz1hat hhat0 (by positivity) hmar
  have hexp : C.cE / F.step N ≤ Real.sqrt (C.cz1 / 8) / Real.sqrt (F.step N) * (C.zhat μ X N - C.Zof μ X N ((C.chain μ X N).jj 1)) := by
    have hdiff : C.dm * (C.η / 2) / Real.sqrt (F.step N) ≤ C.zhat μ X N - C.Zof μ X N ((C.chain μ X N).jj 1) := by
      rw [Zof_eq]; unfold zhat; rw [← sub_div]
      exact div_le_div_of_nonneg_right hlen hs.le
    have hq0 : 0 ≤ Real.sqrt (C.cz1 / 8) / Real.sqrt (F.step N) := by positivity
    calc C.cE / F.step N = Real.sqrt (C.cz1 / 8) / Real.sqrt (F.step N) * (C.dm * (C.η / 2) / Real.sqrt (F.step N)) := by
          rw [div_mul_div_comm, Real.mul_self_sqrt hh0.le]; unfold cE; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiff hq0
  have hmono := Eminus_mono (C.aOf μ X N) hz1 hz2
  calc Eminus (C.aOf μ X N) (C.Zof μ X N ((C.chain μ X N).jj 1))
      ≤ Real.exp (-(Real.sqrt (C.cz1 / 8) / Real.sqrt (F.step N) * (C.zhat μ X N - C.Zof μ X N ((C.chain μ X N).jj 1)))) *
          Eminus (C.aOf μ X N) (C.zhat μ X N) := hdec
    _ ≤ Real.exp (-(C.cE / F.step N)) * Eminus (C.aOf μ X N) z :=
        mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hmono (Eminus_pos _ _).le (Real.exp_pos _).le

/-- `zeta(-eta/2) <= zeta(x_{j_2}) <= 0`: `hat Z <= 0` (the intermediate point is on the recessive patch). -/
lemma zhat_nonpos : C.zhat μ X N ≤ 0 := by
  have hhH1 : F.step N ≤ C.softH1 := hh.trans C.softH2_le_H1
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hμ hX hN hhH1 hV
  have hα := C.abs_alpha_le hX
  have hhat := C.j2_ge hμ hX hN hh hV
  obtain ⟨-, hη, hdm, -⟩ := C.consts_pos
  have hs : 0 < Real.sqrt (F.step N) := Real.sqrt_pos.mpr (step_pos (F := F) N)
  have hmvt := C.zeta_mvt hμ hα (by linarith : -(2 * C.η) ≤ -(C.η / 2)) (by linarith : -(C.η / 2) ≤ uNode (F.step N) ((C.chain μ X N).jj 2) - C.uc μ)
    (by
      have : uNode (F.step N) ((C.chain μ X N).jj 2) ≤ uNode (F.step N) ((C.chain μ X N).jj 2 + 1) :=
        uNode_mono_le (step_pos (F := F) N).le (by omega)
      linarith)
  have hzh : C.zeta μ (F.bandHi μ - X) (-(C.η / 2)) ≤ 0 := by
    have := mul_nonneg hdm.le (sub_nonneg.mpr (by linarith : -(C.η / 2) ≤ uNode (F.step N) ((C.chain μ X N).jj 2) - C.uc μ))
    linarith [hmvt.1]
  unfold zhat
  exact div_nonpos_of_nonpos_of_nonneg hzh hs.le

/-- `E_-(Z_{j_1}) <= exp(-c_E/h)`. -/
lemma Eminus_j1_small :
    Eminus (C.aOf μ X N) (C.Zof μ X N ((C.chain μ X N).jj 1)) ≤ Real.exp (-(C.cE / F.step N)) := by
  have h1 := C.Eminus_j1_decay hμ hX hN hh hV (z := 0) (C.zhat_nonpos hμ hX hN hh hV) le_rfl
  have h2 := Eminus_le_one (C.aOf μ X N) (le_refl (0 : ℝ))
  calc _ ≤ _ := h1
    _ ≤ Real.exp (-(C.cE / F.step N)) * 1 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := mul_one _

end Absorb

end SoftEdgeChart

end FormalResearch.JacobiEigenvectors.Charts
