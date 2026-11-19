module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.ThmAAssemblySoft

/-!
# Paper J, Layer 2: the soft relative window lemma (L2.C9, finding F-BB-5)

Source: Paper J `thmA.tex`, "The relative statement" (soft case: "`T <= -eps` puts `n` off the window `Omega`, where prop:tha-W2 (2) gives `V_n/hat N <= C |hat Psi_n|`"), `lem:cha-PCcoord`, `def:tha-win` (`rho(a)`).

## Proved here (axiom-pinned)

Chain, for a soft chart `C` of a family `Fz` at `p` in `P`, `h = step N`, `alpha = X_s^+(p) - X`, `a = -(mu_0 + S)/h` (`S = sum_{r>=1} h^{2r} mu_{2r}`, `|S| <= R h^2`, `R = (q/2) C_mu`):

1. `window_excl_pure` (pure real analysis): `zeta^2 >= 4 mu_0 + c`, `mu_0 <= C_mu`, `mu_0 >= -L_b h^2`, `h` small give `rho(a) < |zeta/sqrt h|`.  Here `rho^2 <= 4 A + 4 sqrt A + 1`, `A = max(-a, 0)`, and
   `h A <= max(mu_0, 0) + R h^2` (or `A <= R h` for `mu_0 < 0`): the sharp constant `4` against `zeta^2 >= 4 mu_0 + c` leaves the room `c/h` for the `O(h^{-1/2})` rest.
2. `muS0_lower`: `mu_0(alpha) >= -C_{mu0} beta` for `alpha >= -beta` (mean value theorem, `mu_0(0) = 0`, `c_{mu0} <= mu_0' <= C_{mu0}`).  Step 0 gives `alpha >= -Cs0 h^2`, hence `mu_0 >= -C h^2`.
3. `softWindow_excl`: the row `n` with `T(u_n; X) <= -eps` satisfies `zeta^2/4 - mu_0 >= c_T eps` (the new chart field `zeta_T`) inside the collar `|u_n - u_c| <= 2 eta`, and `zeta^2 >= 4 max(mu_0, 0) + c_{z1}` beyond it (`zeta_far_out`):
   so `Z_n` is off the window.  It needs the Step 0 hypothesis `X <= X_s^+ + Cs0 h^2`; **without it the lemma is false** (for `X > X_s^+ + eps` the window contains rows with `T << 0`: the barrier region), so `SoftWindowT` now carries it
   (`ThmAAssemblySoft.lean`: `softUpper_data` returns the `Cs0` of `stepZero` and the bound).
4. `softWindowT_of_chart`: `SoftWindowT CI` for the charts `CI.softUpL` (frozen family) and `CI.softLoL` (the gauge `negFamily`, `T^{neg}(-X; u) = T(X; u)`), from `softWindow_excl` and `|T^{(h)} - T| <= C h` (`frozenT_le`,
   jets `G_1, B_1` bounded; `|X|` bounded through `X_s^+ = f_+(u_c)`, `bandHi_abs_le`).  Premises: `IsCompact K`, `DM F K 1`.

## Differences from the paper / findings

* **New chart field `zeta_T`** (`SoftEdgeChart`, with `cT`, `cT_pos`; `Charts/SoftParabolicCylinder.lean`, "Round 10"): `zeta^2/4 - mu_0 >= c_T (-T)` on the collar where `T <= 0`.  In the paper it is the content of
  `lem:cha-PCcoord (1)`: `Omega_0^2 = zeta^2/4 - mu_0`, `cosh(Omega_0 d_x zeta) = Upsilon_0`, `T = 4 E_0 (1 - Upsilon_0^2)`, `d_x zeta <= d_+`; it was not among the earlier fields (`zeta_far` only constrains `zeta^2` outside `|x| < eta/4`).
* **F-BB-5 refined**: `SoftWindowT` needs the Step 0 premise (above).

## Not formalised

The derivation of `zeta_T` from `cosh(Omega_0 zeta') = Upsilon_0` (it is a chart hypothesis, like the other `zeta_*` fields).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

/-- The smallness constant of `window_excl_pure`. -/
def winK (R Mm Lb : ℝ) : ℝ := 4 * R + 4 * Real.sqrt (Mm + R) + 4 * Real.sqrt R + 1 + 4 * Lb

lemma winK_pos {R Mm Lb : ℝ} (hR : 0 ≤ R) (hLb : 0 ≤ Lb) : 0 < winK R Mm Lb := by
  unfold winK
  have := Real.sqrt_nonneg (Mm + R); have := Real.sqrt_nonneg R
  linarith

lemma rhoWin_sq_le (a : ℝ) : rhoWin a ^ 2 ≤ 4 * max (-a) 0 + 4 * Real.sqrt (max (-a) 0) + 1 := by
  have hA0 : 0 ≤ max (-a) 0 := le_max_right _ _
  set A := max (-a) 0 with hA
  have ht0 := Real.sqrt_nonneg A
  have ht2 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA0
  have hw0 : 0 ≤ (1 + A) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by linarith) _
  have hw1 : (1 + A) ^ (-(1 : ℝ) / 6) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  unfold rhoWin
  rw [← hA]
  nlinarith [mul_le_mul_of_nonneg_left hw1 ht0, mul_le_mul hw1 hw1 hw0 zero_le_one]

set_option maxHeartbeats 1600000 in
/-- **pure window exclusion**: if `zeta^2 >= 4 m0 + c` with `m0 <= Mm`, `m0 >= -Lb h^2`, `a = -(m0 + S)/h`, `|S| <= R h^2`, and `h` small, then `|zeta / sqrt h| > rho(a)`. -/
lemma window_excl_pure {h c R Mm Lb m0 S ζ : ℝ} (hR : 0 ≤ R) (hLb : 0 ≤ Lb) (hc : 0 < c)
    (h0 : 0 < h) (h1 : h ≤ 1) (hs : Real.sqrt h ≤ c / (2 * winK R Mm Lb))
    (hm0u : m0 ≤ Mm) (hm0l : -(Lb * h ^ 2) ≤ m0) (hS : |S| ≤ R * h ^ 2) (hζ : 4 * m0 + c ≤ ζ ^ 2) :
    rhoWin (-(1 / h) * (m0 + S)) < |ζ / Real.sqrt h| := by
  have hK := winK_pos (Mm := Mm) hR hLb
  set s := Real.sqrt h with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr h0
  have hs2 : s ^ 2 = h := Real.sq_sqrt h0.le
  have hs1 : s ≤ 1 := by rw [hsdef]; exact Real.sqrt_le_one.mpr h1  
  have hhs : h ≤ s := by nlinarith
  have hh2s : h ^ 2 ≤ s := by nlinarith [mul_nonneg h0.le h0.le]
  have hKs : winK R Mm Lb * s ≤ c / 2 := by
    rw [le_div_iff₀ (by positivity)] at hs
    nlinarith
  set a := -(1 / h) * (m0 + S) with ha
  have hna : -a = (m0 + S) / h := by rw [ha]; field_simp
  set A := max (-a) 0 with hA
  have hA0 : 0 ≤ A := le_max_right _ _
  set t := Real.sqrt A with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg A
  have ht2 : t ^ 2 = A := Real.sq_sqrt hA0
  have hSu : S ≤ R * h ^ 2 := (le_abs_self S).trans hS
  have hρ := rhoWin_sq_le a
  rw [← hA, ← ht] at hρ
  have hsqM : 0 ≤ Real.sqrt (Mm + R) := Real.sqrt_nonneg _
  have hsqR : 0 ≤ Real.sqrt R := Real.sqrt_nonneg _
  -- key: h * (4A + 4t + 1) < 4 m0 + c
  have key : h * (4 * A + 4 * t + 1) < 4 * m0 + c := by
    rcases le_or_gt 0 m0 with hm | hm
    · have hAu : A ≤ (m0 + R * h ^ 2) / h := by
        apply max_le
        · rw [hna]; exact div_le_div_of_nonneg_right (by linarith) h0.le
        · exact div_nonneg (by nlinarith [sq_nonneg h]) h0.le
      have hhA : h * A ≤ m0 + R * h ^ 2 := by
        rw [le_div_iff₀ h0] at hAu; linarith
      have hhA' : h * A ≤ Mm + R := by nlinarith [sq_nonneg h]
      have hst : s * t ≤ Real.sqrt (Mm + R) := by
        apply le_trans (le_abs_self _) 
        apply Real.abs_le_sqrt
        have : (s * t) ^ 2 = h * A := by rw [mul_pow, hs2, ht2]
        rw [this]; exact hhA'
      have hht : h * t ≤ s * Real.sqrt (Mm + R) := by
        have : h * t = s * (s * t) := by rw [← hs2]; ring
        rw [this]; exact mul_le_mul_of_nonneg_left hst hs0.le
      have e1 : R * h ^ 2 ≤ R * s := mul_le_mul_of_nonneg_left hh2s hR
      have hb : 4 * (R * s) + 4 * (s * Real.sqrt (Mm + R)) + s ≤ c / 2 := by
        have := hKs; unfold winK at this
        nlinarith [mul_nonneg hsqR hs0.le, mul_nonneg hLb hs0.le]
      nlinarith
    · have hAu : A ≤ R * h := by
        apply max_le
        · rw [hna, div_le_iff₀ h0]; nlinarith
        · exact mul_nonneg hR h0.le
      have hhA : h * A ≤ R * h ^ 2 := by
        calc h * A ≤ h * (R * h) := mul_le_mul_of_nonneg_left hAu h0.le
          _ = R * h ^ 2 := by ring
      have hAR : A ≤ R := hAu.trans (mul_le_of_le_one_right hR h1)
      have hst : t ≤ Real.sqrt R := Real.sqrt_le_sqrt hAR
      have e1 : R * h ^ 2 ≤ R * s := mul_le_mul_of_nonneg_left hh2s hR
      have e2 : h * t ≤ s * Real.sqrt R := by
        calc h * t ≤ h * Real.sqrt R := mul_le_mul_of_nonneg_left hst h0.le
          _ ≤ s * Real.sqrt R := mul_le_mul_of_nonneg_right hhs hsqR
      have e3 : Lb * h ^ 2 ≤ Lb * s := mul_le_mul_of_nonneg_left hh2s hLb
      have hb : 4 * (R * s) + 4 * (s * Real.sqrt R) + s + 4 * (Lb * s) ≤ c / 2 := by
        have := hKs; unfold winK at this
        have h5 : 0 ≤ Real.sqrt (Mm + R) * s := mul_nonneg hsqM hs0.le
        linarith
      have e4 : h * (4 * A + 4 * t + 1) = 4 * (h * A) + 4 * (h * t) + h := by ring
      rw [e4]
      linarith
  have hy : 0 ≤ |ζ / s| := abs_nonneg _
  have hy2 : |ζ / s| ^ 2 = ζ ^ 2 / h := by rw [sq_abs, div_pow, hs2]
  by_contra hcon
  replace hcon := not_lt.mp hcon
  have hρ0 : 0 ≤ rhoWin a := by
    unfold rhoWin
    have := Real.sqrt_nonneg (max (-a) 0)
    have : 0 ≤ (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg (by linarith [le_max_right (-a) 0]) _
    linarith
  have h2 : |ζ / s| ^ 2 ≤ rhoWin a ^ 2 := pow_le_pow_left₀ hy hcon 2
  rw [hy2, div_le_iff₀ h0] at h2
  nlinarith

/-- Lower bound of the leading shift for `alpha >= -beta`: `mu_0(alpha) >= -C_{mu0} beta` (`mu_0(0) = 0`, `0 < c_{mu0} <= mu_0' <= C_{mu0}` on `|alpha| <= delta_0`; mean value theorem). -/
lemma muS0_lower {F : SymbolFamily Par} {P : Set Par} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
    (C : SoftEdgeChart F P m q U V Lm) {p : Par} (hp : p ∈ P) {α β : ℝ} (hβ : 0 ≤ β) (hα : |α| ≤ C.δ0) (hαβ : -β ≤ α) :
    -(C.Cmu0 * β) ≤ C.muS 0 p α := by
  have hc0 := C.consts_pos5.1
  have hC0 : 0 ≤ C.Cmu0 := hc0.le.trans C.consts_pos5.2
  have hf := (C.mu0_deriv p hp).1
  have hcont : Continuous (C.muS 0 p) := hf.continuous
  have hdiff : Differentiable ℝ (C.muS 0 p) := hf.differentiable one_ne_zero
  have h0 := C.mu0_zero p hp
  rcases lt_trichotomy α 0 with h | h | h
  · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (C.muS 0 p) h hcont.continuousOn hdiff.differentiableOn
    have hcδ : |c| ≤ C.δ0 := by
      rw [abs_le] at hα ⊢
      constructor <;> linarith [hc.1, hc.2]
    have hb := (C.mu0_slope p hp c hcδ).2
    rw [h0] at hcd
    have e : (0 - C.muS 0 p α) / (0 - α) = C.muS 0 p α / α := by rw [zero_sub, zero_sub, neg_div_neg_eq]
    rw [e] at hcd
    rw [hcd, div_le_iff_of_neg h] at hb
    nlinarith [mul_nonneg hC0 hβ]
  · subst h; rw [h0]; nlinarith [mul_nonneg hC0 hβ]
  · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (C.muS 0 p) h hcont.continuousOn hdiff.differentiableOn
    have hcδ : |c| ≤ C.δ0 := by
      rw [abs_le] at hα ⊢
      constructor <;> linarith [hc.1, hc.2]
    have hb := (C.mu0_slope p hp c hcδ).1
    rw [h0, sub_zero, sub_zero] at hcd
    rw [hcd, le_div_iff₀ h] at hb
    nlinarith [mul_nonneg hC0 hβ]

/-- **Rows with `T <= -eps` are off the soft window** (for any chart, any family): at energies `|X - X_s^+| <= delta_0`, `X <= X_s^+ + Cs0 h^2` (Step 0), for small `h`.
Chain: `zeta^2 >= 4 mu_0 + c` at the row (`zeta_T` inside the collar `|u - u_c| <= 2 eta`, with `T <= -eps`; `zeta_far_out` outside it), `a = -(mu_0 + O(h^2))/h` (`muS_bd`),
`mu_0 >= -C h^2` (`muS0_lower`), hence `Z^2 = zeta^2/h > rho(a)^2` (`window_excl_pure`). -/
theorem softWindow_excl {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
    (C : SoftEdgeChart Fz P m q U V Lm) (Cs0 ε : ℝ) (hε : 0 < ε) :
    ∃ h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, Fz.step N ≤ h1 → ∀ X : ℝ, |X - Fz.bandHi p| ≤ C.δ0 →
      X ≤ Fz.bandHi p + Cs0 * Fz.step N ^ 2 → ∀ n ∈ rowsOf N,
      Tfun Fz.L (Fz.G 0 p) (Fz.B 0 p) X (uNode (Fz.step N) n) ≤ -ε → n ∉ softWindow C p X N := by
  have hCmu0 : 0 ≤ C.Cmu := C.consts_pos2.1
  have hcT := C.cT_pos
  have hcz1 := C.consts_pos2.2
  set R : ℝ := ((q / 2 : ℕ) : ℝ) * C.Cmu with hRdef
  have hR : 0 ≤ R := by positivity
  set Cs' : ℝ := max Cs0 0 with hCs'
  have hCs'0 : 0 ≤ Cs' := le_max_right _ _
  have hC0 : 0 ≤ C.Cmu0 := C.consts_pos5.1.le.trans C.consts_pos5.2
  set Lb : ℝ := C.Cmu0 * Cs' with hLb
  have hLb0 : 0 ≤ Lb := by positivity
  set c : ℝ := min (4 * C.cT * ε) C.cz1 with hc
  have hcpos : 0 < c := lt_min (by positivity) hcz1
  set K : ℝ := winK R C.Cmu Lb with hK
  have hKpos : 0 < K := winK_pos (Mm := C.Cmu) hR hLb0
  refine ⟨min 1 ((c / (2 * K)) ^ 2), lt_min one_pos (by positivity), ?_⟩
  intro p hp N hN X hX hX0 n hn hT
  have hpos : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  set h := Fz.step N with hh
  have hN1 : h ≤ 1 := hN.trans (min_le_left _ _)
  have hN2 : h ≤ (c / (2 * K)) ^ 2 := hN.trans (min_le_right _ _)
  have hsq : Real.sqrt h ≤ c / (2 * K) := by
    calc Real.sqrt h ≤ Real.sqrt ((c / (2 * K)) ^ 2) := Real.sqrt_le_sqrt hN2
      _ = c / (2 * K) := Real.sqrt_sq (by positivity)
  set α : ℝ := Fz.bandHi p - X with hαdef
  have hα : |α| ≤ C.δ0 := by rw [hαdef, abs_sub_comm]; exact hX
  have hαlow : -(Cs' * h ^ 2) ≤ α := by
    have : Cs0 * h ^ 2 ≤ Cs' * h ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg h)
    rw [hαdef]; linarith
  have hm0l : -(Lb * h ^ 2) ≤ C.muS 0 p α := by
    have := muS0_lower C hp (by positivity : 0 ≤ Cs' * h ^ 2) hα hαlow
    have e : C.Cmu0 * (Cs' * h ^ 2) = Lb * h ^ 2 := by rw [hLb]; ring
    linarith
  have hm0u : C.muS 0 p α ≤ C.Cmu := by
    have := C.muS_bd 0 (by simp) p hp α hα
    exact (le_abs_self _).trans this
  have hS : |∑ r ∈ Finset.Icc 1 (q / 2), h ^ (2 * r) * C.muS r p α| ≤ R * h ^ 2 := by
    calc |∑ r ∈ Finset.Icc 1 (q / 2), h ^ (2 * r) * C.muS r p α|
        ≤ ∑ r ∈ Finset.Icc 1 (q / 2), |h ^ (2 * r) * C.muS r p α| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ Finset.Icc 1 (q / 2), h ^ 2 * C.Cmu := by
          apply Finset.sum_le_sum
          intro r hr
          rw [Finset.mem_Icc] at hr
          rw [abs_mul, abs_of_nonneg (pow_nonneg hpos.le _)]
          exact mul_le_mul (pow_le_pow_of_le_one hpos.le hN1 (by omega)) (C.muS_bd r (Finset.mem_Icc.mpr ⟨by omega, hr.2⟩) p hp α hα)
            (abs_nonneg _) (sq_nonneg _)
      _ = R * h ^ 2 := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hRdef]
          simp only [Nat.add_sub_cancel]
          ring
  -- the row
  have hn0 : (0 : ℤ) ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ (N : ℤ) := (Finset.mem_Icc.mp hn).2
  have hLs : h * ((N : ℝ) + 1) = Fz.L := step_mul_succ_aux Fz N
  have hu0 : 0 ≤ uNode h n := by
    unfold uNode
    have : (0 : ℝ) ≤ n := by exact_mod_cast hn0
    positivity
  have huL : uNode h n ≤ Fz.L := by
    unfold uNode
    have : (n : ℝ) ≤ N := by exact_mod_cast hnN
    nlinarith
  have hζ : 4 * C.muS 0 p α + c ≤ C.zeta p α (uNode h n - C.uc p) ^ 2 := by
    by_cases hx : |uNode h n - C.uc p| ≤ 2 * C.η
    · have hT' : Tfun Fz.L (Fz.G 0 p) (Fz.B 0 p) (Fz.bandHi p - α) (C.uc p + (uNode h n - C.uc p)) ≤ 0 := by
        have e1 : Fz.bandHi p - α = X := by rw [hαdef]; ring
        have e2 : C.uc p + (uNode h n - C.uc p) = uNode h n := by ring
        rw [e1, e2]; linarith
      have := C.zeta_T p hp α hα (uNode h n - C.uc p) hx (by linarith) (by linarith) hT'
      have e1 : Fz.bandHi p - α = X := by rw [hαdef]; ring
      have e2 : C.uc p + (uNode h n - C.uc p) = uNode h n := by ring
      rw [e1, e2] at this
      have h4 : 4 * C.cT * ε ≤ 4 * (C.cT * (-Tfun Fz.L (Fz.G 0 p) (Fz.B 0 p) X (uNode h n))) := by nlinarith
      have h5 : c ≤ 4 * C.cT * ε := min_le_left _ _
      linarith
    · have hx' : 2 * C.η ≤ |uNode h n - C.uc p| := le_of_lt (not_le.mp hx)
      have := C.zeta_far_out p hp α hα (uNode h n - C.uc p) hx' (by linarith) (by linarith)
      have h5 : c ≤ C.cz1 := min_le_right _ _
      have h6 := le_max_left (C.muS 0 p α) 0
      linarith
  intro hmem
  have hle := (Finset.mem_filter.mp hmem).2
  have key : rhoWin (C.aOf p X N) < |C.Zof p X N n| := by
    unfold SoftEdgeChart.aOf SoftEdgeChart.Zof aPC
    exact window_excl_pure hR hLb0 hcpos hpos hN1 hsq hm0u hm0l hS hζ
  exact absurd hle (not_le.mpr key)

/-! ### From the chart lemma to `SoftWindowT` -/

/-- Bounds of the jets of order `0` and `1` of `G_0, G_1, B_0, B_1` on `K x [0, L]`. -/
lemma jets01_bound {F : SymbolFamily Par} {K : Set Par} (hK : IsCompact K) (hD : DM F K 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ μ ∈ K, ∀ s ∈ Icc 0 F.L,
      |F.G 0 μ s| ≤ M ∧ |F.G 1 μ s| ≤ M ∧ |F.B 0 μ s| ≤ M ∧ |F.B 1 μ s| ≤ M := by
  have hreg : ∀ j ≤ 1, JetReg (F.G j) K F.L (regBudget 1 - 10 * (j / 2)) ∧ JetReg (F.B j) K F.L (regBudget 1 - 10 * (j / 2)) := hD.reg
  obtain ⟨a0, ha0⟩ := jet_bound hK (hreg 0 (by omega)).1 (k := 0) (Nat.zero_le _)
  obtain ⟨a1, ha1⟩ := jet_bound hK (hreg 1 (by omega)).1 (k := 0) (Nat.zero_le _)
  obtain ⟨b0, hb0⟩ := jet_bound hK (hreg 0 (by omega)).2 (k := 0) (Nat.zero_le _)
  obtain ⟨b1, hb1⟩ := jet_bound hK (hreg 1 (by omega)).2 (k := 0) (Nat.zero_le _)
  refine ⟨|a0| + |a1| + |b0| + |b1|, by positivity, fun μ hμ s hs => ?_⟩
  have h0 := ha0 μ hμ s hs
  have h1 := ha1 μ hμ s hs
  have h2 := hb0 μ hμ s hs
  have h3 := hb1 μ hμ s hs
  simp only [iteratedDerivWithin_zero] at h0 h1 h2 h3
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    linarith [le_abs_self a0, le_abs_self a1, le_abs_self b0, le_abs_self b1, abs_nonneg a0, abs_nonneg a1, abs_nonneg b0, abs_nonneg b1]

/-- `T` of the frozen principal symbols is `O(h)`-above `T` of those of `F` (uniformly for `|X| <= MX`). -/
lemma frozenT_le {F : SymbolFamily Par} {K : Set Par} {M MX : ℝ} (Kidx : ℕ)
    (hMj : ∀ μ ∈ K, ∀ s ∈ Icc 0 F.L, |F.G 0 μ s| ≤ M ∧ |F.G 1 μ s| ≤ M ∧ |F.B 0 μ s| ≤ M ∧ |F.B 1 μ s| ≤ M)
    {μ : Par} (hμ : μ ∈ K) {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) {X : ℝ} (hX : |X| ≤ MX) {u : ℝ} (hu : u ∈ Icc 0 F.L) :
    Tfun F.L ((frozenFamily F Kidx).G 0 (μ, h)) ((frozenFamily F Kidx).B 0 (μ, h)) X u ≤
      Tfun F.L (F.G 0 μ) (F.B 0 μ) X u + h * (4 * F.L ^ 2 * M + M * (2 * MX + 2 * M + M)) := by
  rw [frozen_G0, frozen_B0]
  have := tfun_frozen_close (L := F.L) (G0 := F.G 0 μ) (G1 := F.G 1 μ) (B0 := F.B 0 μ) (B1 := F.B 1 μ) (M := M) (MX := MX) (X := X)
    hh0 hh1 (fun s hs => (hMj μ hμ s hs).2.1) (fun s hs => (hMj μ hμ s hs).2.2.2) (fun s hs => (hMj μ hμ s hs).2.2.1) hX hu
  have := (abs_le.mp this).2
  linarith

/-- `|X_s^+| <= M + 2 L sqrt M` when `|G_0|, |B_0| <= M` on `[0, L]` (at the fold `u_c`, `X_s^+ = f_+(u_c)`). -/
lemma bandHi_abs_le {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
    (C : SoftEdgeChart Fz P m q U V Lm) {M : ℝ} (hM : 0 ≤ M)
    (hG : ∀ p ∈ P, ∀ u ∈ Icc 0 Fz.L, |Fz.G 0 p u| ≤ M) (hB : ∀ p ∈ P, ∀ u ∈ Icc 0 Fz.L, |Fz.B 0 p u| ≤ M) :
    ∀ p ∈ P, |Fz.bandHi p| ≤ M + 2 * (Fz.L * Real.sqrt M) := by
  intro p hp
  obtain ⟨hu0, hu1, hf⟩ := C.uc_spec p hp
  rw [← hf]
  have hu : C.uc p ∈ Icc 0 Fz.L := ⟨hu0.le, hu1.le⟩
  have hL := Fz.L_pos
  unfold fPlus
  have hE : E0 Fz.L (Fz.G 0 p) (C.uc p) ≤ Fz.L ^ 2 * M := by
    unfold E0
    have a : C.uc p * (Fz.L - C.uc p) ≤ Fz.L ^ 2 := by nlinarith [hu.1, hu.2]
    have b : 0 ≤ C.uc p * (Fz.L - C.uc p) := mul_nonneg hu.1 (by linarith [hu.2])
    have c := (le_abs_self _).trans (hG p hp _ hu)
    calc C.uc p * (Fz.L - C.uc p) * Fz.G 0 p (C.uc p) ≤ C.uc p * (Fz.L - C.uc p) * M := mul_le_mul_of_nonneg_left c b
      _ ≤ Fz.L ^ 2 * M := mul_le_mul_of_nonneg_right a hM
  have hs : Real.sqrt (E0 Fz.L (Fz.G 0 p) (C.uc p)) ≤ Fz.L * Real.sqrt M := by
    calc Real.sqrt (E0 Fz.L (Fz.G 0 p) (C.uc p)) ≤ Real.sqrt (Fz.L ^ 2 * M) := Real.sqrt_le_sqrt hE
      _ = Fz.L * Real.sqrt M := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hL.le]
  have hs0 := Real.sqrt_nonneg (E0 Fz.L (Fz.G 0 p) (C.uc p))
  calc |Fz.B 0 p (C.uc p) + 2 * Real.sqrt (E0 Fz.L (Fz.G 0 p) (C.uc p))|
      ≤ |Fz.B 0 p (C.uc p)| + |2 * Real.sqrt (E0 Fz.L (Fz.G 0 p) (C.uc p))| := abs_add_le _ _
    _ ≤ M + 2 * (Fz.L * Real.sqrt M) := by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt (E0 Fz.L (Fz.G 0 p) (C.uc p)))]
        linarith [hB p hp _ hu]

lemma uNode_mem_Icc_rows (F : SymbolFamily Par) {N : ℕ} {n : ℤ} (hn : n ∈ rowsOf N) : uNode (F.step N) n ∈ Icc 0 F.L := by
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hn0 : (0 : ℤ) ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ (N : ℤ) := (Finset.mem_Icc.mp hn).2
  have hLs : F.step N * ((N : ℝ) + 1) = F.L := step_mul_succ_aux F N
  unfold uNode
  have h0 : (0 : ℝ) ≤ n := by exact_mod_cast hn0
  have h1 : (n : ℝ) ≤ N := by exact_mod_cast hnN
  exact ⟨by positivity, by nlinarith⟩

lemma tfun_neg (L : ℝ) (G B : ℝ → ℝ) (X u : ℝ) : Tfun L G (fun s => -B s) (-X) u = Tfun L G B X u := by
  unfold Tfun; ring

set_option maxHeartbeats 4000000 in
/-- **The soft relative window lemma `SoftWindowT`, proved** (finding F-BB-5; `T(u_n; X) <= -eps` puts `n` off the soft window `Omega` for small `h`, at energies with Step 0): from `softWindow_excl`
for the charts `CI.softUpL` (frozen family) and `CI.softLoL` (its gauge `negFamily`, where `T^{neg}(-X; u) = T(X; u)`), and `|T^{(h)} - T| <= C h` (`frozenT_le`). -/
theorem softWindowT_of_chart {F : SymbolFamily Par} {K : Set Par} {m Kidx : ℕ} {t0 : ℝ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (hK : IsCompact K) (hD : DM F K 1) (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) : SoftWindowT CI := by
  obtain ⟨M, hM0, hMj⟩ := jets01_bound hK hD
  set M1 : ℝ := (1 + |t0|) * M with hM1
  have hM10 : 0 ≤ M1 := by positivity
  have hfr : ∀ p ∈ paramSet K t0, ∀ u ∈ Icc 0 F.L,
      |(frozenFamily F Kidx).G 0 p u| ≤ M1 ∧ |(frozenFamily F Kidx).B 0 p u| ≤ M1 := by
    rintro ⟨μ, t⟩ ⟨hμ, ht⟩ u hu
    have htt : |t| ≤ |t0| := abs_le_abs ht.2 (by linarith [ht.1])
    obtain ⟨a, b, c, d⟩ := hMj μ hμ u hu
    have e1 : (frozenFamily F Kidx).G 0 (μ, t) u = F.G 0 μ u + t * F.G 1 μ u := by simp [frozenFamily]
    have e2 : (frozenFamily F Kidx).B 0 (μ, t) u = F.B 0 μ u + t * F.B 1 μ u := by simp [frozenFamily]
    have k1 : |t * F.G 1 μ u| ≤ |t0| * M := by
      rw [abs_mul]; exact mul_le_mul htt b (abs_nonneg _) (abs_nonneg _)
    have k2 : |t * F.B 1 μ u| ≤ |t0| * M := by
      rw [abs_mul]; exact mul_le_mul htt d (abs_nonneg _) (abs_nonneg _)
    constructor
    · rw [e1]; calc _ ≤ |F.G 0 μ u| + |t * F.G 1 μ u| := abs_add_le _ _
        _ ≤ M1 := by rw [hM1]; linarith
    · rw [e2]; calc _ ≤ |F.B 0 μ u| + |t * F.B 1 μ u| := abs_add_le _ _
        _ ≤ M1 := by rw [hM1]; linarith
  have hbU := bandHi_abs_le CI.softUpL hM10 (fun p hp u hu => (hfr p hp u hu).1) (fun p hp u hu => (hfr p hp u hu).2)
  have hbL := bandHi_abs_le CI.softLoL hM10 (fun p hp u hu => (hfr p hp u hu).1)
    (fun p hp u hu => by
      have := (hfr p hp u hu).2
      show |-(frozenFamily F Kidx).B 0 p u| ≤ M1
      rw [abs_neg]; exact this)
  set MBH : ℝ := M1 + 2 * (F.L * Real.sqrt M1) with hMBH
  have hMBH0 : 0 ≤ MBH := by have := F.L_pos; positivity
  set MX : ℝ := MBH + max CI.softUpL.δ0 CI.softLoL.δ0 with hMX
  have hδu := CI.softUpL.consts_pos.1
  have hδl := CI.softLoL.consts_pos.1
  have hMX0 : 0 ≤ MX := by
    have : 0 ≤ max CI.softUpL.δ0 CI.softLoL.δ0 := le_max_of_le_left hδu.le
    positivity
  set Cc : ℝ := 4 * F.L ^ 2 * M + M * (2 * MX + 2 * M + M) with hCc
  have hCc0 : 0 ≤ Cc := by have := F.L_pos; positivity
  have hεhalf : ∀ ε : ℝ, 0 < ε → ∀ h : ℝ, h ≤ ε / (2 * (Cc + 1)) → h * Cc ≤ ε / 2 := by
    intro ε hε h hh
    calc h * Cc ≤ (ε / (2 * (Cc + 1))) * Cc := mul_le_mul_of_nonneg_right hh hCc0
      _ ≤ ε / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  refine ⟨?_, ?_⟩
  · intro Cs0 ε hε
    obtain ⟨h1, h1p, Hex⟩ := softWindow_excl CI.softUpL Cs0 (ε / 2) (by positivity)
    refine ⟨min (min h1 1) (ε / (2 * (Cc + 1))), lt_min (lt_min h1p one_pos) (by positivity), ?_⟩
    intro μ hμ N hN hNt X hX hX0 n hn hT
    have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have hp : (μ, F.step N) ∈ paramSet K t0 := ⟨hμ, ⟨by linarith, hNt⟩⟩
    have hN1 : F.step N ≤ h1 := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hN2 : F.step N ≤ 1 := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hN3 : F.step N ≤ ε / (2 * (Cc + 1)) := hN.trans (min_le_right _ _)
    have hXb : |X| ≤ MX := by
      have h1' : |(frozenFamily F Kidx).bandHi (μ, F.step N)| ≤ MBH := hbU (μ, F.step N) hp
      have h2' : |X| ≤ |(frozenFamily F Kidx).bandHi (μ, F.step N)| + |X - (frozenFamily F Kidx).bandHi (μ, F.step N)| := by
        calc |X| = |(frozenFamily F Kidx).bandHi (μ, F.step N) + (X - (frozenFamily F Kidx).bandHi (μ, F.step N))| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      have h3' : CI.softUpL.δ0 ≤ max CI.softUpL.δ0 CI.softLoL.δ0 := le_max_left _ _
      rw [hMX]
      have : |X - (frozenFamily F Kidx).bandHi (μ, F.step N)| ≤ CI.softUpL.δ0 := hX
      linarith
    have hTc : Tfun F.L ((frozenFamily F Kidx).G 0 (μ, F.step N)) ((frozenFamily F Kidx).B 0 (μ, F.step N)) X (uNode (F.step N) n) ≤
        Tfun F.L (F.G 0 μ) (F.B 0 μ) X (uNode (F.step N) n) + F.step N * Cc :=
      frozenT_le (F := F) (K := K) (M := M) (MX := MX) Kidx hMj hμ hpos.le hN2 hXb (uNode_mem_Icc_rows F hn)
    have h4 := hεhalf ε hε _ hN3
    refine Hex (μ, F.step N) hp N hN1 X hX hX0 n hn (le_trans hTc ?_)
    linarith
  · intro Cs0 ε hε
    obtain ⟨h1, h1p, Hex⟩ := softWindow_excl CI.softLoL Cs0 (ε / 2) (by positivity)
    refine ⟨min (min h1 1) (ε / (2 * (Cc + 1))), lt_min (lt_min h1p one_pos) (by positivity), ?_⟩
    intro μ hμ N hN hNt X hX hX0 n hn hT
    have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have hp : (μ, F.step N) ∈ paramSet K t0 := ⟨hμ, ⟨by linarith, hNt⟩⟩
    have hN1 : F.step N ≤ h1 := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hN2 : F.step N ≤ 1 := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hN3 : F.step N ≤ ε / (2 * (Cc + 1)) := hN.trans (min_le_right _ _)
    have hXb : |X| ≤ MX := by
      have h1' : |(negFamily (frozenFamily F Kidx)).bandHi (μ, F.step N)| ≤ MBH := hbL (μ, F.step N) hp
      have h2' : |-X| ≤ |(negFamily (frozenFamily F Kidx)).bandHi (μ, F.step N)| +
          |-X - (negFamily (frozenFamily F Kidx)).bandHi (μ, F.step N)| := by
        calc |-X| = |(negFamily (frozenFamily F Kidx)).bandHi (μ, F.step N) + (-X - (negFamily (frozenFamily F Kidx)).bandHi (μ, F.step N))| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      have h3' : CI.softLoL.δ0 ≤ max CI.softUpL.δ0 CI.softLoL.δ0 := le_max_right _ _
      rw [hMX, ← abs_neg X]
      have : |-X - (negFamily (frozenFamily F Kidx)).bandHi (μ, F.step N)| ≤ CI.softLoL.δ0 := hX
      linarith
    have hTc : Tfun F.L ((frozenFamily F Kidx).G 0 (μ, F.step N)) ((frozenFamily F Kidx).B 0 (μ, F.step N)) X (uNode (F.step N) n) ≤
        Tfun F.L (F.G 0 μ) (F.B 0 μ) X (uNode (F.step N) n) + F.step N * Cc :=
      frozenT_le (F := F) (K := K) (M := M) (MX := MX) Kidx hMj hμ hpos.le hN2 hXb (uNode_mem_Icc_rows F hn)
    have h4 := hεhalf ε hε _ hN3
    have e : Tfun (negFamily (frozenFamily F Kidx)).L ((negFamily (frozenFamily F Kidx)).G 0 (μ, F.step N))
        ((negFamily (frozenFamily F Kidx)).B 0 (μ, F.step N)) (-X) (uNode (F.step N) n) =
        Tfun F.L ((frozenFamily F Kidx).G 0 (μ, F.step N)) ((frozenFamily F Kidx).B 0 (μ, F.step N)) X (uNode (F.step N) n) :=
      tfun_neg F.L _ _ X _
    refine Hex (μ, F.step N) hp N hN1 (-X) hX hX0 n hn (le_trans (le_of_eq e) (le_trans hTc ?_))
    linarith

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softWindow_excl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softWindow_excl

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softWindowT_of_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softWindowT_of_chart

end FormalResearch.JacobiEigenvectors.TheoremA

end
