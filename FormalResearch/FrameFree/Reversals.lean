import FormalResearch.FrameFree.GateOverlap
import FormalResearch.FrameFree.ExchangeSharing
import FormalResearch.FrameFree.M4Support
import FormalResearch.FrameFree.Unify
import FormalResearch.FrameFree.Arithmetic

/-!
# Paper P: reversals, gate gaps and tensorisation arithmetic

Elementary, fully proved parts of `thm:ratefails`, `thm:ratefailregion`, `thm:calgeom-fourgate`,
`thm:calgeom-tensorisation`, `cor:calgeom-spin1extensive`, `thm:m4exponent`, `thm:expceiling` and
`cor:fourdecoh`/`cor:fourgapfloor` (paper `ResearchNotes/QI/antiunitary_occupation/paper/long`).

`ξ_inv` is **not** defined in this file (`HasXiInv`, the limit of `-(1/k) log P_e(k)`, is in
`XiInvUnconditional`, which restates these results with exact `ξ_inv`).  Wherever the argument here uses it, `ξ`
is a real number and the hypotheses are exactly the inequalities the paper uses: the support lower bound
`-log F_C ≤ ξ`, the tensorised or ceiling upper bound, or the envelope converse `e^{-ξ} ≥ 𝒲(C₃,C₂)`
(chain steps (1)-(3) of the paper, `EnvelopeAtStar`).  The one recalled input is a hypothesis:
`FKΘ M₄ ≤ 4/9` (R7).

**Proved here.**
* Strict reversal against a calibrated ruler (`strictReversal_ruler_iff`, `reversal_of_gap_ruler`,
  `gap_of_reversal_ruler`); the exchange gates are a ruler on `[0, log 2]` (`exchange_law`,
  `exchange_ruler`), in the repository's own objects (`FCs_id_eq`, `FKΘ_psiEx`, `FCΘ_psiEx`).
* Region of `thm:ratefailregion`: `F_K = cos²(2c₃)` (`region_FK`), the exact equivalence
  `sup_u [x + (q/2)(u-1)]²/G(u)² ≤ x²  ⟺  1 + xy ≤ 2x²` (`rlf_le_iff`, i.e. (R3) is exactly a gap in
  the envelope), the gap `ξ < C_K` (`region_gap`) and the reversal (`region_reversal`).
* `U_* = (9/20, 19/50, 8/25)`: `C_K = -log((1+cos(32/25))/2) = 0.4410..` (`ratefails_gap`) and the
  four-gate reversal against the exchange gates (`fourgate_reversal`, `fourgate_three_tenths`), from
  rational enclosures of `cos` and `log` (no interval arithmetic).  Self-certified replacement of the
  paper's interval-arithmetic constant: `ξ < 0.4283` (`ratefails_certified`).
* Eight qubits and blocks of four (`Psi8_values`, `eight_qubit_reversal`, `blocks_gap`,
  `blocks_exponent`, `m4_exponent`).
* Tensorisation arithmetic (`prod_add_le`, `prod_harmonic_le`, `RateLE_prod_half`, `additive_of_tie`).
* `cor:fourdecoh`, `cor:fourgapfloor` glue and numerics (`fourdecoh_glue`, `fourdecoh_value`,
  `fourgapfloor_arith`), `thm:expceiling` arithmetic (`expceiling_arith`, `critical_exponent`).

Here `ξ` is a free real variable bounded by the paper's inequalities.  The operational exponent `ξ_inv`
(`XiInv.HasXiInv`) and the discharged forms of these statements are in `XiInvUnconditional`, `ConverseXi`
and `AchiralCritical` (which proves `thm:expceiling` for critical four-qubit states).

**Not formalised.** Chain steps (1)-(3) (torus reduction, split-filter converse, envelope); the
190-competitor condition (R1) and the wedge/volume statement of `thm:ratefailregion`; the Helstrom
inequality `P_⊗ ≥ ½ ∏ P_i`; the interval-arithmetic constant `B_* = 0.42776639`.
-/

open Real Filter Topology
namespace FormalResearch.FrameFree.Reversals
open FormalResearch.FrameFree

/-- Strict reversal (`def:reversal`), on the numbers `(C_K, ξ)`: the first pair is more chiral and
less detectable. -/
def StrictReversal (Cψ ξψ Cφ ξφ : ℝ) : Prop := Cφ < Cψ ∧ ξψ < ξφ

theorem strictReversal_ruler_iff (Cψ ξψ r : ℝ) :
    StrictReversal Cψ ξψ r r ↔ ξψ < r ∧ r < Cψ := by
  unfold StrictReversal; tauto

theorem reversal_of_gap_ruler {Cψ ξψ : ℝ} (_h : ξψ < Cψ) {r : ℝ} (h1 : ξψ < r) (h2 : r < Cψ) :
    StrictReversal Cψ ξψ r r := (strictReversal_ruler_iff _ _ _).2 ⟨h1, h2⟩

theorem gap_of_reversal_ruler {Cψ ξψ r : ℝ} (h : StrictReversal Cψ ξψ r r) : ξψ < Cψ :=
  lt_trans ((strictReversal_ruler_iff _ _ _).1 h).1 ((strictReversal_ruler_iff _ _ _).1 h).2

noncomputable def CKg (c : Fin 3 → ℝ) : ℝ := -Real.log (FKmag (dgate c))
noncomputable def CKex (s : ℝ) : ℝ := Real.log (2 / (1 + s))

theorem δg_exchange (θ : ℝ) : δg (fun _ => θ / 2) = |cos (2 * θ)| := by
  unfold δg
  have : 4 * (θ / 2) = 2 * θ := by ring
  simp [this]

theorem CKg_eq (c : Fin 3 → ℝ) : CKg c = Real.log (2 / (1 + δg c)) := (CK_gate c).1
theorem CKg_exchange (θ : ℝ) : CKg (fun _ => θ / 2) = CKex |cos (2 * θ)| := by
  rw [CKg_eq, δg_exchange]; rfl

noncomputable def cStar : Fin 3 → ℝ := ![9 / 20, 19 / 50, 8 / 25]

theorem delta_cStar : δg cStar = cos (32 / 25) := by
  have e : δg cStar = max (max |cos (9 / 5)| |cos (38 / 25)|) |cos (32 / 25)| := by
    unfold δg
    simp only [cStar, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    norm_num
  have hp := Real.pi_gt_d2
  have hpu := Real.pi_lt_d2
  have hpl := Real.pi_pos
  have h32 : 0 ≤ cos (32 / 25) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have h38 : 0 ≤ cos (38 / 25) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have h38' : cos (38 / 25) < cos (32 / 25) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num) (by linarith) (by norm_num)
  have h95 : |cos (9 / 5)| < cos (32 / 25) := by
    have hneg : cos (9 / 5) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    rw [abs_of_neg hneg, ← Real.cos_pi_sub]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num) (by linarith) (by linarith)
  rw [e, abs_of_nonneg h32, abs_of_nonneg h38]
  rw [max_eq_right (max_le h95.le h38'.le)]

theorem FKmag_gate_δ (c : Fin 3 → ℝ) : FKmag (dgate c) = (1 + δg c) / 2 := FKmag_gate c

theorem FKmag_cStar : FKmag (dgate cStar) = (1 + cos (32 / 25)) / 2 := by
  rw [FKmag_gate_δ, delta_cStar]

theorem CKg_cStar : CKg cStar = CKex (cos (32 / 25)) := by
  rw [CKg_eq, delta_cStar]; rfl

/-! ### Elementary enclosures -/

/-- `cos (32/25)` lies in `(0.28669, 0.28672)`: `cos(32/25) = sin(π/2 − 32/25)`, Taylor bounds
(`sin x > x - x³/6` and `|sin x - (x - x³/6)| ≤ x⁵/100`) and `3.141592 < π < 3.141593`. -/
theorem cos_32_25_bounds : (0.28669 : ℝ) < cos (32 / 25) ∧ cos (32 / 25) < 0.28672 := by
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hy : cos (32 / 25) = sin (π / 2 - 32 / 25) := (Real.sin_pi_div_two_sub _).symm
  rw [hy]
  set y := π / 2 - 32 / 25 with hydef
  have hy0 : (0.290796 : ℝ) < y := by rw [hydef]; linarith
  have hy1 : y < 0.2907965 := by rw [hydef]; linarith
  have hyabs : |y| ≤ 1 := by rw [abs_of_pos (by linarith)]; linarith
  constructor
  · have := Real.sin_gt_sub_cube (x := y) (by linarith)
    nlinarith [mul_pos (sub_pos.2 hy0) (sub_pos.2 hy0), mul_pos (sub_pos.2 hy0) (by linarith : (0:ℝ) < y)]
  · have h := (abs_le.1 (Real.sin_bound hyabs)).2
    rw [abs_of_pos (by linarith : 0 < y)] at h
    have h5 : y ^ 5 ≤ 0.2907965 ^ 5 := pow_le_pow_left₀ (by linarith) hy1.le 5
    have h3 : (0.290796 : ℝ) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) hy0.le 3
    nlinarith

theorem log_ratio_ge (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    2 * ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1) ≤ log ((1 + x) / (1 - x)) := by
  have := Real.sum_range_le_log_div h0 h1 n
  linarith

theorem log_ratio_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    log ((1 + x) / (1 - x)) ≤
      2 * ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1) + 2 * (x ^ (2 * n + 1) / (1 - x ^ 2)) := by
  have := Real.log_div_le_sum_range_add h0 h1 n
  linarith

theorem log_20_13_bounds : (0.43078 : ℝ) < log (20 / 13) ∧ log (20 / 13) < 0.43079 := by
  have e : (1 + 7 / 33) / (1 - 7 / 33) = (20 / 13 : ℝ) := by norm_num
  have h1 := log_ratio_ge (7 / 33) (by norm_num) (by norm_num) 5
  have h2 := log_ratio_le (7 / 33) (by norm_num) (by norm_num) 5
  rw [e] at h1 h2
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith

theorem CKex_eq_ratio (c : ℝ) (hc : -1 < c) :
    CKex c = log ((1 + (1 - c) / (3 + c)) / (1 - (1 - c) / (3 + c))) := by
  unfold CKex
  congr 1
  have h3 : (3 + c) ≠ 0 := by linarith
  have h1 : (1 + c) ≠ 0 := by linarith
  have h2 : (2 + 2 * c) ≠ 0 := by intro h; apply h1; linarith
  rw [show 1 + (1 - c) / (3 + c) = 4 / (3 + c) by field_simp; ring,
    show 1 - (1 - c) / (3 + c) = (2 + 2 * c) / (3 + c) by field_simp; ring]
  field_simp
  ring

theorem CKex_ge_sum (c : ℝ) (hc : -1 < c) (hc1 : c ≤ 1) (n : ℕ) :
    2 * ∑ i ∈ Finset.range n, ((1 - c) / (3 + c)) ^ (2 * i + 1) / (2 * i + 1) ≤ CKex c := by
  rw [CKex_eq_ratio c hc]
  have h3 : 0 < 3 + c := by linarith
  refine log_ratio_ge _ (div_nonneg (by linarith) h3.le) ?_ n
  rw [div_lt_one h3]; linarith

theorem CKex_le_sum (c : ℝ) (hc : -1 < c) (hc1 : c ≤ 1) (n : ℕ) :
    CKex c ≤ 2 * ∑ i ∈ Finset.range n, ((1 - c) / (3 + c)) ^ (2 * i + 1) / (2 * i + 1) +
      2 * (((1 - c) / (3 + c)) ^ (2 * n + 1) / (1 - ((1 - c) / (3 + c)) ^ 2)) := by
  rw [CKex_eq_ratio c hc]
  have h3 : 0 < 3 + c := by linarith
  refine log_ratio_le _ (div_nonneg (by linarith) h3.le) ?_ n
  rw [div_lt_one h3]; linarith

theorem CKex_anti {a b : ℝ} (ha : -1 < a) (hab : a ≤ b) : CKex b ≤ CKex a := by
  unfold CKex
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  exact Real.log_le_log (div_pos two_pos h2) (div_le_div_of_nonneg_left two_pos.le h1 (by linarith))

theorem CKex_strictAnti {a b : ℝ} (ha : -1 < a) (hab : a < b) : CKex b < CKex a := by
  unfold CKex
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  exact Real.log_lt_log (div_pos two_pos h2) (div_lt_div_of_pos_left two_pos h1 (by linarith))

/-- `CKex s > B` iff `1 + s < 2 e^{-B}`. -/
theorem CKex_gt_iff {B s : ℝ} (hs : -1 < s) : B < CKex s ↔ 1 + s < 2 * exp (-B) := by
  unfold CKex
  have h1 : 0 < 1 + s := by linarith
  rw [Real.lt_log_iff_exp_lt (div_pos two_pos h1), lt_div_iff₀ h1, Real.exp_neg]
  have := Real.exp_pos B
  constructor
  · intro h
    rw [lt_mul_inv_iff₀ this]; nlinarith
  · intro h
    rw [lt_mul_inv_iff₀ this] at h; nlinarith

theorem CKex_028672_ge : (0.44105 : ℝ) ≤ CKex 0.28672 := by
  have h := CKex_ge_sum 0.28672 (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem CKex_028669_le : CKex 0.28669 ≤ (0.44108 : ℝ) := by
  have h := CKex_le_sum 0.28669 (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem CKex_030392_gt : (0.42776639 : ℝ) < CKex 0.30392 := by
  have h := CKex_ge_sum 0.30392 (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem CKex_three_tenths : CKex (3 / 10) = log (20 / 13) := by
  unfold CKex; norm_num

/-! ### `thm:ratefails` and `thm:calgeom-fourgate` -/

/-- The chiral distance of `U_*` (`c = (9/20, 19/50, 8/25)`) is `0.4411…`, and it exceeds any
`ξ ≤ B_* = 0.42776639` by more than `0.0132`.  (`thm:ratefails`, the `C_K` half and the comparison
with the bound; `ξ` is a free variable here.) -/
theorem ratefails_gap {ξ : ℝ} (hξ : ξ ≤ 0.42776639) :
    0.4410 < CKg cStar ∧ CKg cStar < 0.4411 ∧ 0.0132 < CKg cStar - ξ := by
  obtain ⟨hc1, hc2⟩ := cos_32_25_bounds
  rw [CKg_cStar]
  have a1 : CKex 0.28672 ≤ CKex (cos (32 / 25)) := CKex_anti (by linarith) hc2.le
  have a2 : CKex (cos (32 / 25)) ≤ CKex 0.28669 := CKex_anti (by norm_num) hc1.le
  have b1 := CKex_028672_ge
  have b2 := CKex_028669_le
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **`thm:calgeom-fourgate`**, the exact part.  Let `ξ` be (any upper bound for) the exponent of
`U_*`, `ξ ≤ B`; let `s = |cos 2θ|` of an exchange gate with `cos(32/25) < s` and `B < log(2/(1+s))`
(equivalently `1 + s < 2 e^{-B}`).  Then `U_*` is strictly more chiral and strictly less detectable
than the exchange gate, whose `ξ = C_K = log(2/(1+s))` (`thm:heis`). -/
theorem fourgate_reversal {ξ B s : ℝ} (hξ : ξ ≤ B) (hs : cos (32 / 25) < s) (hB : B < CKex s) :
    StrictReversal (CKg cStar) ξ (CKex s) (CKex s) := by
  have hc := cos_32_25_bounds.1
  rw [CKg_cStar]
  exact ⟨CKex_strictAnti (by linarith) hs, lt_of_le_of_lt hξ hB⟩

theorem fourgate_reversal_exp {ξ B s : ℝ} (hξ : ξ ≤ B) (hs : cos (32 / 25) < s)
    (hB : 1 + s < 2 * exp (-B)) : StrictReversal (CKg cStar) ξ (CKex s) (CKex s) := by
  have hc := cos_32_25_bounds.1
  exact fourgate_reversal hξ hs ((CKex_gt_iff (by linarith)).2 hB)

/-- **`thm:calgeom-fourgate`** with the paper's numbers: `ξ(U_*) ≤ B_* = 0.42776639` and every
`0.28672 ≤ s ≤ 0.30392` (the paper's window `0.28672 < s < 0.30392`, closed: `cos(32/25) < 0.28672`
is proved here and `0.42776639 < log(2/1.30392)`). -/
theorem fourgate_reversal_window {ξ s : ℝ} (hξ : ξ ≤ 0.42776639) (h1 : 0.28672 ≤ s)
    (h2 : s ≤ 0.30392) : StrictReversal (CKg cStar) ξ (CKex s) (CKex s) := by
  refine fourgate_reversal hξ (lt_of_lt_of_le cos_32_25_bounds.2 h1) ?_
  exact lt_of_lt_of_le CKex_030392_gt (CKex_anti (by linarith) h2)

/-- At `s = 3/10`: `C_K(U_θ) = log(20/13) ∈ (0.43078, 0.43079)` and both margins exceed `0.0030`. -/
theorem fourgate_three_tenths {ξ : ℝ} (hξ : ξ ≤ 0.42776639) :
    CKex (3 / 10) = log (20 / 13) ∧ 0.43078 < CKex (3 / 10) ∧ CKex (3 / 10) < 0.43079 ∧
      0.0030 < CKg cStar - CKex (3 / 10) ∧ 0.0030 < CKex (3 / 10) - ξ ∧
      StrictReversal (CKg cStar) ξ (CKex (3 / 10)) (CKex (3 / 10)) := by
  obtain ⟨l1, l2⟩ := log_20_13_bounds
  have e := CKex_three_tenths
  obtain ⟨g1, g2, g3⟩ := ratefails_gap hξ
  refine ⟨e, by rw [e]; exact l1, by rw [e]; exact l2, by rw [e]; linarith, by rw [e]; linarith, ?_⟩
  exact fourgate_reversal hξ
    (lt_of_lt_of_le cos_32_25_bounds.2 (by norm_num : (0.28672 : ℝ) ≤ 3 / 10))
    (by rw [e]; linarith)

/-- `R(u)` of the envelope: `√(ℓ² + 4q²u²(u²−1))`, `ℓ = 1 − xy`, `q = x − y`. -/
noncomputable def Rr (x y u : ℝ) : ℝ :=
  Real.sqrt ((1 - x * y) ^ 2 + 4 * (x - y) ^ 2 * u ^ 2 * (u ^ 2 - 1))

/-- `G(u)² = ½(L + R(u))`, `L = 1 + xy`. -/
noncomputable def Gsq (x y u : ℝ) : ℝ := ((1 + x * y) + Rr x y u) / 2

/-- The ratio `[x + (q/2)(u−1)]² / G(u)²` whose supremum over `u ≥ 1` is `𝒲(x,y)`. -/
noncomputable def rlf (x y u : ℝ) : ℝ := (x + (x - y) / 2 * (u - 1)) ^ 2 / Gsq x y u

theorem Rr_nonneg (x y u : ℝ) : 0 ≤ Rr x y u := Real.sqrt_nonneg _

theorem Gsq_pos {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (u : ℝ) : 0 < Gsq x y u := by
  unfold Gsq
  have := Rr_nonneg x y u
  have : 0 < 1 + x * y := by positivity
  linarith

theorem rlf_one {x y : ℝ} (hxy : x * y < 1) : rlf x y 1 = x ^ 2 := by
  unfold rlf Gsq Rr
  have : Real.sqrt ((1 - x * y) ^ 2 + 4 * (x - y) ^ 2 * 1 ^ 2 * (1 ^ 2 - 1)) = 1 - x * y := by
    rw [show (1 - x * y) ^ 2 + 4 * (x - y) ^ 2 * 1 ^ 2 * (1 ^ 2 - 1) = (1 - x * y) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  rw [this]
  have : ((1 + x * y) + (1 - x * y)) / 2 = 1 := by ring
  rw [this]; ring

/-- The exact identity behind the comparison `ℓ ≤ 2qx` (coefficients in `t = u - 1`). -/
theorem rlf_key (x y t : ℝ) :
    x ^ 4 * ((1 - x * y) ^ 2 + 4 * (x - y) ^ 2 * (1 + t) ^ 2 * ((1 + t) ^ 2 - 1))
      - (2 * (x + (x - y) / 2 * t) ^ 2 - x ^ 2 * (1 + x * y)) ^ 2
    = t * (4 * (x - y) * x ^ 3 * (2 * (x - y) * x - (1 - x * y)))
      + t ^ 2 * ((x - y) ^ 2 * x ^ 2 * (20 * x ^ 2 - (1 - x * y) - 4))
      + t ^ 3 * ((x - y) ^ 2 * x * (16 * x ^ 3 - 2 * (x - y)))
      + t ^ 4 * ((x - y) ^ 2 * (4 * x ^ 4 - (x - y) ^ 2 / 4)) := by
  ring

theorem Rr_sq (x y u : ℝ) (hu : 1 ≤ u) :
    Rr x y u ^ 2 = (1 - x * y) ^ 2 + 4 * (x - y) ^ 2 * u ^ 2 * (u ^ 2 - 1) := by
  unfold Rr
  apply Real.sq_sqrt
  have : 0 ≤ u ^ 2 - 1 := by nlinarith
  positivity

theorem rlf_le_of {x y u : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (h : 2 * (x + (x - y) / 2 * (u - 1)) ^ 2 - x ^ 2 * (1 + x * y) ≤ x ^ 2 * Rr x y u) :
    rlf x y u ≤ x ^ 2 := by
  unfold rlf
  rw [div_le_iff₀ (Gsq_pos hx hy u)]
  unfold Gsq
  nlinarith [h]

theorem lt_rlf_of {x y u : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (h : x ^ 2 * Rr x y u < 2 * (x + (x - y) / 2 * (u - 1)) ^ 2 - x ^ 2 * (1 + x * y)) :
    x ^ 2 < rlf x y u := by
  unfold rlf
  rw [lt_div_iff₀ (Gsq_pos hx hy u)]
  unfold Gsq
  nlinarith [h]

theorem rlf_H_of_le {x y : ℝ} (hy : 0 < y) (hyx : y < x) (hx1 : x < 1)
    (hall : ∀ u : ℝ, 1 ≤ u → rlf x y u ≤ x ^ 2) : 1 + x * y ≤ 2 * x ^ 2 := by
  have hx : 0 < x := lt_trans hy hyx
  have hq : 0 < x - y := sub_pos.2 hyx
  have hxy : x * y < 1 := by nlinarith
  by_contra hH
  push Not at hH
  have hc1 : 4 * (x - y) * x ^ 3 * (2 * (x - y) * x - (1 - x * y)) < 0 := by
    have : 2 * (x - y) * x - (1 - x * y) < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg (by positivity) this
  obtain ⟨c1, hc1def⟩ : ∃ c1, c1 = 4 * (x - y) * x ^ 3 * (2 * (x - y) * x - (1 - x * y)) := ⟨_, rfl⟩
  obtain ⟨c2, hc2def⟩ : ∃ c2, c2 = (x - y) ^ 2 * x ^ 2 * (20 * x ^ 2 - (1 - x * y) - 4) := ⟨_, rfl⟩
  obtain ⟨c3, hc3def⟩ : ∃ c3, c3 = (x - y) ^ 2 * x * (16 * x ^ 3 - 2 * (x - y)) := ⟨_, rfl⟩
  obtain ⟨c4, hc4def⟩ : ∃ c4, c4 = (x - y) ^ 2 * (4 * x ^ 4 - (x - y) ^ 2 / 4) := ⟨_, rfl⟩
  rw [← hc1def] at hc1
  have hcont : ContinuousAt (fun t : ℝ => c1 + c2 * t + c3 * t ^ 2 + c4 * t ^ 3) 0 := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), (fun t : ℝ => c1 + c2 * t + c3 * t ^ 2 + c4 * t ^ 3) t <
      (fun _ : ℝ => (0 : ℝ)) t :=
    hcont.eventually_lt continuousAt_const (by simpa using hc1)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = δ / 2 := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  have hp : c1 + c2 * t + c3 * t ^ 2 + c4 * t ^ 3 < 0 := by
    have := hδ' (y := t) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht0]; linarith)
    simpa using this
  have hkey := rlf_key x y t
  rw [← hc1def, ← hc2def, ← hc3def, ← hc4def] at hkey
  have hneg : x ^ 4 * ((1 - x * y) ^ 2 + 4 * (x - y) ^ 2 * (1 + t) ^ 2 * ((1 + t) ^ 2 - 1))
      - (2 * (x + (x - y) / 2 * t) ^ 2 - x ^ 2 * (1 + x * y)) ^ 2 < 0 := by
    rw [hkey]
    have : t * c1 + t ^ 2 * c2 + t ^ 3 * c3 + t ^ 4 * c4 =
        t * (c1 + c2 * t + c3 * t ^ 2 + c4 * t ^ 3) := by ring
    rw [this]
    exact mul_neg_of_pos_of_neg ht0 hp
  have hu : 1 ≤ 1 + t := by linarith
  have hR := Rr_sq x y (1 + t) hu
  have hE : 0 < 2 * (x + (x - y) / 2 * t) ^ 2 - x ^ 2 * (1 + x * y) := by
    have h1 : x ≤ x + (x - y) / 2 * t := by
      have : 0 ≤ (x - y) / 2 * t := by positivity
      linarith
    have h2 : x ^ 2 ≤ (x + (x - y) / 2 * t) ^ 2 := pow_le_pow_left₀ hx.le h1 2
    have h3 : 0 < x ^ 2 * (1 - x * y) := mul_pos (pow_pos hx 2) (sub_pos.2 hxy)
    nlinarith [h2, h3]
  have hlt : x ^ 2 * Rr x y (1 + t) <
      2 * (x + (x - y) / 2 * ((1 + t) - 1)) ^ 2 - x ^ 2 * (1 + x * y) := by
    rw [show (1 + t) - 1 = t by ring]
    by_contra hcon
    push Not at hcon
    have := pow_le_pow_left₀ hE.le hcon 2
    have e2 : (x ^ 2 * Rr x y (1 + t)) ^ 2 = x ^ 4 * Rr x y (1 + t) ^ 2 := by ring
    rw [e2, hR] at this
    exact absurd (lt_of_lt_of_le (sub_neg.1 hneg) this) (lt_irrefl _)
  have h1 := lt_rlf_of hx hy.le hlt
  have h2 := hall (1 + t) hu
  exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)

theorem rlf_le_of_H {x y : ℝ} (hy : 0 < y) (hyx : y < x) (hx1 : x < 1)
    (H : 1 + x * y ≤ 2 * x ^ 2) : ∀ u : ℝ, 1 ≤ u → rlf x y u ≤ x ^ 2 := by
  have hx : 0 < x := lt_trans hy hyx
  have hq : 0 < x - y := sub_pos.2 hyx
  have hxy : x * y < 1 := by nlinarith
  intro u hu
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ u = 1 + t := ⟨u - 1, by linarith, by ring⟩
  have hx2 : 1 / 2 ≤ x ^ 2 := by linarith [mul_pos hx hy]
  have hxy' : x * y ≤ x * x := by nlinarith
  have n1 : 0 ≤ 4 * (x - y) * x ^ 3 * (2 * (x - y) * x - (1 - x * y)) :=
    mul_nonneg (by positivity) (by nlinarith)
  have n2 : 0 ≤ (x - y) ^ 2 * x ^ 2 * (20 * x ^ 2 - (1 - x * y) - 4) :=
    mul_nonneg (by positivity) (by nlinarith)
  have hq1 : x - y ≤ x := by linarith
  have n3 : 0 ≤ (x - y) ^ 2 * x * (16 * x ^ 3 - 2 * (x - y)) := by
    refine mul_nonneg (by positivity) ?_
    have : x * (8 * x ^ 2 - 1) ≥ 0 := mul_nonneg hx.le (by linarith)
    nlinarith
  have n4 : 0 ≤ (x - y) ^ 2 * (4 * x ^ 4 - (x - y) ^ 2 / 4) := by
    refine mul_nonneg (by positivity) ?_
    have h2 : (x - y) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hq.le hq1 2
    have : x ^ 2 * (4 * x ^ 2 - 1 / 4) ≥ 0 := mul_nonneg (by positivity) (by linarith)
    nlinarith
  apply rlf_le_of hx hy.le
  rw [show (1 + t) - 1 = t by ring]
  by_contra hcon
  push Not at hcon
  have h0 : 0 ≤ x ^ 2 * Rr x y (1 + t) := by have := Rr_nonneg x y (1 + t); positivity
  have hR := Rr_sq x y (1 + t) (by linarith)
  have e2 : (x ^ 2 * Rr x y (1 + t)) ^ 2 = x ^ 4 * Rr x y (1 + t) ^ 2 := by ring
  have hlt : (x ^ 2 * Rr x y (1 + t)) ^ 2 <
      (2 * (x + (x - y) / 2 * t) ^ 2 - x ^ 2 * (1 + x * y)) ^ 2 :=
    pow_lt_pow_left₀ hcon h0 (by norm_num)
  rw [e2, hR] at hlt
  have hkey := rlf_key x y t
  have hsum : 0 ≤ t * (4 * (x - y) * x ^ 3 * (2 * (x - y) * x - (1 - x * y)))
    + t ^ 2 * ((x - y) ^ 2 * x ^ 2 * (20 * x ^ 2 - (1 - x * y) - 4))
    + t ^ 3 * ((x - y) ^ 2 * x * (16 * x ^ 3 - 2 * (x - y)))
    + t ^ 4 * ((x - y) ^ 2 * (4 * x ^ 4 - (x - y) ^ 2 / 4)) :=
    add_nonneg (add_nonneg (add_nonneg (mul_nonneg ht n1) (mul_nonneg (pow_nonneg ht 2) n2))
      (mul_nonneg (pow_nonneg ht 3) n3)) (mul_nonneg (pow_nonneg ht 4) n4)
  have hd : 0 ≤ x ^ 4 * ((1 - x * y) ^ 2 + 4 * (x - y) ^ 2 * (1 + t) ^ 2 * ((1 + t) ^ 2 - 1))
      - (2 * (x + (x - y) / 2 * t) ^ 2 - x ^ 2 * (1 + x * y)) ^ 2 := by
    rw [hkey]; exact hsum
  exact absurd (sub_nonneg.1 hd) (not_le.2 hlt)

/-- **Step (4) of the chain for `thm:ratefailregion` (a)** (`𝒲(x,y) = x²` iff `2x² ≥ 1 + xy`), in
the sup-free form: `rlf x y u ≤ x²` for all `u ≥ 1` iff `1 + xy ≤ 2x²`.  Here `0 < y < x < 1`
(`x = C_3 > y = C_2`, i.e. (R0)); with `2C_3² − 1 = cos 4c_3` the failure of `1 + xy ≤ 2x²` is (R3). -/
theorem rlf_le_iff {x y : ℝ} (hy : 0 < y) (hyx : y < x) (hx1 : x < 1) :
    (∀ u : ℝ, 1 ≤ u → rlf x y u ≤ x ^ 2) ↔ 1 + x * y ≤ 2 * x ^ 2 :=
  ⟨rlf_H_of_le hy hyx hx1, rlf_le_of_H hy hyx hx1⟩

/-! ### The envelope at `U_*` -/

/-- Two-sided Taylor enclosure of `cos 2z = 1 - 2 sin² z` for `0 < z ≤ 1`. -/
theorem cos_two_enclosure {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) (hpos : 0 ≤ z - z ^ 3 / 6) :
    1 - 2 * (z - z ^ 3 / 6 + z ^ 5 / 100) ^ 2 ≤ cos (2 * z) ∧
      cos (2 * z) ≤ 1 - 2 * (z - z ^ 3 / 6) ^ 2 := by
  have hlo := Real.sin_gt_sub_cube hz0
  have hhi := (abs_le.1 (Real.sin_bound (x := z) (by rw [abs_of_pos hz0]; exact hz1))).2
  rw [abs_of_pos hz0] at hhi
  have hc : cos (2 * z) = 1 - 2 * sin z ^ 2 := by
    rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq z]
  rw [hc]
  constructor
  · nlinarith [mul_self_nonneg (sin z)]
  · nlinarith [mul_self_nonneg (sin z)]

theorem cos_16_25_bounds : (0.80208 : ℝ) < cos (16 / 25) ∧ cos (16 / 25) < 0.80214 := by
  obtain ⟨h1, h2⟩ := cos_two_enclosure (z := 8 / 25) (by norm_num) (by norm_num) (by norm_num)
  rw [show 2 * (8 / 25 : ℝ) = 16 / 25 by norm_num] at h1 h2
  norm_num at h1 h2
  constructor <;> linarith

theorem cos_19_25_bounds : (0.72481 : ℝ) < cos (19 / 25) ∧ cos (19 / 25) < 0.72494 := by
  obtain ⟨h1, h2⟩ := cos_two_enclosure (z := 19 / 50) (by norm_num) (by norm_num) (by norm_num)
  rw [show 2 * (19 / 50 : ℝ) = 19 / 25 by norm_num] at h1 h2
  norm_num at h1 h2
  constructor <;> linarith

/-- Certified lower bound for the envelope ratio at `u = 1.37`, from rational enclosures of
`x = C_3`, `y = C_2` (monotone bounds on each piece; `√` bounded by `0.4634`). -/
theorem rlf_lower_of_bounds {x y : ℝ} (hxl : 0.80208 < x) (hxu : x < 0.80214)
    (hyl : 0.72481 < y) (hyu : y < 0.72494) : 0.6517 < rlf x y (137 / 100) := by
  have hx : 0 < x := by linarith
  have hy : 0 < y := by linarith
  have hxy_lo : 0.80208 * 0.72481 ≤ x * y := mul_le_mul hxl.le hyl.le (by norm_num) hx.le
  have hxy_hi : x * y ≤ 0.80214 * 0.72494 := mul_le_mul hxu.le hyu.le hy.le (by norm_num)
  have hl0 : 0 ≤ 1 - x * y := by nlinarith
  have hl1 : 1 - x * y ≤ 1 - 0.80208 * 0.72481 := by linarith
  have hq0 : 0 ≤ x - y := by linarith
  have hq1 : x - y ≤ 0.80214 - 0.72481 := by linarith
  have hlsq : (1 - x * y) ^ 2 ≤ (1 - 0.80208 * 0.72481) ^ 2 := pow_le_pow_left₀ hl0 hl1 2
  have hqsq : (x - y) ^ 2 ≤ (0.80214 - 0.72481) ^ 2 := pow_le_pow_left₀ hq0 hq1 2
  have hR : Rr x y (137 / 100) ≤ 0.4634 := by
    unfold Rr
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    have : 4 * (x - y) ^ 2 * (137 / 100) ^ 2 * ((137 / 100) ^ 2 - 1) ≤
        4 * (0.80214 - 0.72481) ^ 2 * (137 / 100) ^ 2 * ((137 / 100) ^ 2 - 1) := by
      have h : (0 : ℝ) ≤ 4 * (137 / 100) ^ 2 * ((137 / 100) ^ 2 - 1) := by norm_num
      nlinarith [mul_le_mul_of_nonneg_left hqsq h]
    have h2 : (1 - 0.80208 * 0.72481 : ℝ) ^ 2 +
        4 * (0.80214 - 0.72481) ^ 2 * (137 / 100) ^ 2 * ((137 / 100) ^ 2 - 1) ≤ 0.4634 ^ 2 := by
      norm_num
    linarith
  have hN : 0.8163509 ≤ x + (x - y) / 2 * (137 / 100 - 1) := by
    norm_num; linarith
  have hGpos := Gsq_pos hx hy.le (137 / 100)
  unfold rlf
  rw [lt_div_iff₀ hGpos]
  unfold Gsq
  have hN2 : (0.8163509 : ℝ) ^ 2 ≤ (x + (x - y) / 2 * (137 / 100 - 1)) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hN 2
  have : (1 + x * y + Rr x y (137 / 100)) / 2 ≤ (1 + 0.80214 * 0.72494 + 0.4634) / 2 := by linarith
  have h3 : (0.6517 : ℝ) * ((1 + 0.80214 * 0.72494 + 0.4634) / 2) < 0.8163509 ^ 2 := by norm_num
  nlinarith

/-! ### The region of `thm:ratefailregion` -/

/-- Cosines of the shifted angles stay strictly below `cos 4z`:
`z < w < π/4 − z` gives `|cos 4w| < cos 4z`. -/
theorem abs_cos_four_lt {z w : ℝ} (hz : 0 ≤ z) (hzw : z < w) (hw : w < π / 4 - z) :
    |cos (4 * w)| < cos (4 * z) := by
  have hp := Real.pi_pos
  rw [abs_lt]
  constructor
  · have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 4 * w) (y := π - 4 * z) (by linarith)
      (by linarith) (by linarith)
    rw [Real.cos_pi_sub] at h
    linarith
  · exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)

/-- **`thm:ratefailregion`, the rotation-overlap part.**  On the region `|c₃| < c₂ < c₁`,
`c₁ + |c₃| < π/4` (the set where (R0) and (R1) hold, by part (b)), the Weyl-vertex maximum is
attained by the double transposition: `δ = cos 4c₃`, `F_K = C₃² = cos²(2c₃)` and
`C_K = -log C₃²`.  (Here `c 0, c 1, c 2` are `c₁, c₂, c₃`.)  This is `thm:gatefk` plus the
trigonometric comparison; the 190 competing vertices of (R1) are not needed for the value. -/
theorem region_FK (c : Fin 3 → ℝ) (h1 : |c 2| < c 1) (h2 : c 1 < c 0) (h3 : c 0 + |c 2| < π / 4) :
    δg c = cos (4 * c 2) ∧ FKmag (dgate c) = cos (2 * c 2) ^ 2 ∧
      CKg c = -Real.log (cos (2 * c 2) ^ 2) := by
  have hz : 0 ≤ |c 2| := abs_nonneg _
  have hc2 : cos (4 * c 2) = cos (4 * |c 2|) := by
    rw [show 4 * c 2 = 4 * c 2 by rfl]
    rcases abs_cases (c 2) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, show 4 * -c 2 = -(4 * c 2) by ring, Real.cos_neg]
  have a0 : |cos (4 * c 0)| < cos (4 * |c 2|) :=
    abs_cos_four_lt hz (by linarith) (by linarith)
  have a1 : |cos (4 * c 1)| < cos (4 * |c 2|) :=
    abs_cos_four_lt hz h1 (by linarith)
  have a2 : |cos (4 * c 2)| = cos (4 * |c 2|) := by
    rw [hc2]
    exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩)
  rw [← hc2] at a0 a1 a2
  have hδ : δg c = cos (4 * c 2) := by
    unfold δg
    rw [a2]
    exact max_eq_right (max_le a0.le a1.le)
  have hFK : FKmag (dgate c) = cos (2 * c 2) ^ 2 := by
    rw [FKmag_gate_δ, hδ, show 4 * c 2 = 2 * (2 * c 2) by ring, Real.cos_two_mul]
    ring
  refine ⟨hδ, hFK, ?_⟩
  unfold CKg; rw [hFK]

theorem rlf_pos {x y : ℝ} (hyx : y < x) (hy : 0 ≤ y) {u : ℝ} (hu : 1 ≤ u) : 0 < rlf x y u := by
  have hx : 0 < x := lt_of_le_of_lt hy hyx
  unfold rlf
  refine div_pos ?_ (Gsq_pos hx hy u)
  have : 0 < x + (x - y) / 2 * (u - 1) := by
    have : 0 ≤ (x - y) / 2 * (u - 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  positivity

/-- **`thm:ratefailregion` (a), the part that is elementary.**  For a gate `c` of the region with
`0 < |c₃|` and (R3) `C₂C₃ > cos 4c₃`, (i) the envelope ratio `rlf C₃ C₂ u` exceeds `F_K = C₃²` at
some `u ≥ 1`, so that `𝒲(C₃,C₂) > C₃²`; (ii) whenever `ξ` satisfies the converse
`rlf C₃ C₂ u ≤ e^{-ξ}` (the paper's chain steps (1)–(3), `e^{-ξ_inv} ≥ 𝒲`, which is **not**
formalised), `C_K − ξ ≥ log(rlf/F_K)`, and `ξ < C_K` as soon as it holds for all `u ≥ 1`. -/
theorem region_gap (c : Fin 3 → ℝ) (h0 : 0 < |c 2|) (h1 : |c 2| < c 1) (h2 : c 1 < c 0)
    (h3 : c 0 + |c 2| < π / 4) (hR3 : cos (4 * c 2) < cos (2 * c 1) * cos (2 * c 2)) :
    (∃ u : ℝ, 1 ≤ u ∧ FKmag (dgate c) < rlf (cos (2 * c 2)) (cos (2 * c 1)) u) ∧
    (∀ ξ u : ℝ, 1 ≤ u → rlf (cos (2 * c 2)) (cos (2 * c 1)) u ≤ exp (-ξ) →
      Real.log (rlf (cos (2 * c 2)) (cos (2 * c 1)) u / FKmag (dgate c)) ≤ CKg c - ξ) ∧
    (∀ ξ : ℝ, (∀ u : ℝ, 1 ≤ u → rlf (cos (2 * c 2)) (cos (2 * c 1)) u ≤ exp (-ξ)) →
      ξ < CKg c) := by
  obtain ⟨-, hFK, hCK⟩ := region_FK c h1 h2 h3
  have hp := Real.pi_pos
  have hz : 0 ≤ |c 2| := abs_nonneg _
  have hcz : cos (2 * c 2) = cos (2 * |c 2|) := by
    rcases abs_cases (c 2) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, show 2 * -c 2 = -(2 * c 2) by ring, Real.cos_neg]
  have hy0 : 0 < cos (2 * c 1) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hyx : cos (2 * c 1) < cos (2 * c 2) := by
    rw [hcz]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have hx1 : cos (2 * c 2) < 1 := by
    rw [hcz, ← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num) (by linarith) (by linarith)
  have hH : ¬ (1 + cos (2 * c 2) * cos (2 * c 1) ≤ 2 * cos (2 * c 2) ^ 2) := by
    intro hH
    have e : cos (4 * c 2) = 2 * cos (2 * c 2) ^ 2 - 1 := by
      rw [show 4 * c 2 = 2 * (2 * c 2) by ring, Real.cos_two_mul]
    nlinarith
  have hne := mt (rlf_H_of_le hy0 hyx hx1) hH
  push Not at hne
  obtain ⟨u0, hu0, hlt⟩ := hne
  have hxpos : 0 < cos (2 * c 2) := lt_trans hy0 hyx
  have key : ∀ ξ u : ℝ, 1 ≤ u → rlf (cos (2 * c 2)) (cos (2 * c 1)) u ≤ exp (-ξ) →
      Real.log (rlf (cos (2 * c 2)) (cos (2 * c 1)) u / FKmag (dgate c)) ≤ CKg c - ξ := by
    intro ξ u hu h
    have hpos := rlf_pos hyx hy0.le hu
    have hxx : 0 < cos (2 * c 2) ^ 2 := pow_pos hxpos 2
    rw [hFK, hCK, Real.log_div hpos.ne' hxx.ne']
    have := Real.log_le_log hpos h
    rw [Real.log_exp] at this
    linarith
  refine ⟨⟨u0, hu0, by rw [hFK]; exact hlt⟩, key, ?_⟩
  intro ξ hξ
  have hpos := rlf_pos hyx hy0.le hu0
  have hxx : 0 < cos (2 * c 2) ^ 2 := pow_pos hxpos 2
  have h1 := key ξ u0 hu0 (hξ u0 hu0)
  have h2 : 0 < Real.log (rlf (cos (2 * c 2)) (cos (2 * c 1)) u0 / FKmag (dgate c)) := by
    apply Real.log_pos
    rw [hFK, lt_div_iff₀ hxx]; linarith
  linarith

/-! ### `U_*` is in the region, and a self-certified exponent bound -/

theorem cStar_zero : cStar 0 = 9 / 20 := by simp [cStar]
theorem cStar_one : cStar 1 = 19 / 50 := by simp [cStar]
theorem cStar_two : cStar 2 = 8 / 25 := by simp [cStar]

/-- `U_*` lies in the region of `thm:ratefailregion`: `0 < |c₃| < c₂ < c₁`, `c₁ + |c₃| < π/4`,
and (R3) holds. -/
theorem cStar_in_region :
    0 < |cStar 2| ∧ |cStar 2| < cStar 1 ∧ cStar 1 < cStar 0 ∧ cStar 0 + |cStar 2| < π / 4 ∧
      cos (4 * cStar 2) < cos (2 * cStar 1) * cos (2 * cStar 2) := by
  rw [cStar_zero, cStar_one, cStar_two]
  have hp := Real.pi_gt_d2
  obtain ⟨a1, a2⟩ := cos_16_25_bounds
  obtain ⟨b1, b2⟩ := cos_19_25_bounds
  obtain ⟨c1, c2⟩ := cos_32_25_bounds
  refine ⟨by norm_num [abs_of_pos], by norm_num [abs_of_pos], by norm_num, ?_, ?_⟩
  · rw [abs_of_pos (by norm_num : (0 : ℝ) < 8 / 25)]; linarith
  · rw [show 4 * (8 / 25 : ℝ) = 32 / 25 by norm_num, show 2 * (19 / 50 : ℝ) = 19 / 25 by norm_num,
      show 2 * (8 / 25 : ℝ) = 16 / 25 by norm_num]
    nlinarith [mul_pos (sub_pos.2 a1) (sub_pos.2 b1)]

/-- The converse input of `thm:ratefails`, the only unformalised ingredient: the paper's chain
(torus reduction, split-filter converse, two torus positions) gives
`e^{-ξ_inv(ψ_{U_*}, ψ_{U_*^{-1}})} ≥ 𝒲(C₃, C₂)`, hence in particular this inequality at
the single point `u = 1.37`. -/
def EnvelopeAtStar (ξ : ℝ) : Prop :=
  rlf (cos (16 / 25)) (cos (19 / 25)) (137 / 100) ≤ exp (-ξ)

theorem CKex_03034 : CKex 0.3034 = -Real.log 0.6517 := by
  unfold CKex
  rw [← Real.log_inv]; norm_num

theorem CKex_03034_le : CKex 0.3034 ≤ 0.4283 := by
  have h := CKex_le_sum 0.3034 (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **`thm:ratefails`, self-certified form** (no interval arithmetic): from the envelope bound at
`u = 1.37` (see `EnvelopeAtStar`), `ξ < -log 0.6517 = CKex 0.3034 < 0.4283`, which is strictly
below `C_K(U_*) = 0.4410…` (the paper's interval-certified constant is `0.42776639`). -/
theorem ratefails_certified {ξ : ℝ} (h : EnvelopeAtStar ξ) :
    ξ < CKex 0.3034 ∧ ξ < 0.4283 ∧ 0.0127 < CKg cStar - ξ := by
  have hlow : (0.6517 : ℝ) < rlf (cos (16 / 25)) (cos (19 / 25)) (137 / 100) :=
    rlf_lower_of_bounds cos_16_25_bounds.1 cos_16_25_bounds.2 cos_19_25_bounds.1 cos_19_25_bounds.2
  have h1 : (0.6517 : ℝ) < exp (-ξ) := lt_of_lt_of_le hlow h
  have h2 : Real.log 0.6517 < -ξ := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]; exact h1
  have h3 : ξ < CKex 0.3034 := by rw [CKex_03034]; linarith
  have h4 := CKex_03034_le
  obtain ⟨g1, g2, g3⟩ := ratefails_gap (ξ := 0.42776639) le_rfl
  refine ⟨h3, by linarith, ?_⟩
  linarith

/-- **`thm:calgeom-fourgate`, self-certified**: `U_*` against the exchange gate with
`0.28672 ≤ s < 0.3034`, from `EnvelopeAtStar` alone. -/
theorem fourgate_reversal_certified {ξ s : ℝ} (h : EnvelopeAtStar ξ) (h1 : 0.28672 ≤ s)
    (h2 : s < 0.3034) : StrictReversal (CKg cStar) ξ (CKex s) (CKex s) := by
  have hξ := (ratefails_certified h).1
  have hs : -1 < s := by linarith
  exact fourgate_reversal hξ.le (lt_of_lt_of_le cos_32_25_bounds.2 h1)
    (CKex_strictAnti hs h2)


open FormalResearch.FrameFree.NQubit in
/-- Independent frames: `F_C^{id}` of `Sharing` is `F_C` of `Ceilings` (the two definitions differ
only in the harmless side condition `‖gφ‖² ≠ 0`). -/
theorem FCs_id_eq {n : ℕ} (ψ φ : Ψ n) (h : nsq φ ≠ 0) :
    Sharing.FCs (id : Fin n → Fin n) ψ φ = Ceilings.FC ψ φ := by
  unfold Sharing.FCs Ceilings.FC
  apply le_antisymm
  · refine csSup_le (Sharing.fiSet_nonempty _ _ _) ?_
    rintro r ⟨v, hv, rfl⟩
    by_cases h0 : nsq (rot (fun i => v (id i)) φ) = 0
    · rw [h0, div_zero]; exact Ceilings.FC_nonneg ψ φ
    · exact le_csSup (Ceilings.FCset_bddAbove ψ φ) ⟨fun i => v (id i), fun i => hv _, h0, rfl⟩
  · refine csSup_le_csSup (Sharing.fiSet_bddAbove _ _ _) (Ceilings.FCset_nonempty ψ φ h) ?_
    rintro r ⟨g, hg, -, rfl⟩
    exact ⟨g, hg, rfl⟩

open FormalResearch.FrameFree.NQubit (Ψ FKΘ CK tens nsq Θ)

/-! ### The exchange-gate Choi probes (`thm:heis`), in the repository's own objects -/

/-- `F_K(ψ_{U_θ}) = cos² θ` for `0 ≤ θ ≤ π/4` (independent frames). -/
theorem FKΘ_psiEx {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4) :
    FKΘ (Sharing.psiEx θ) = Real.cos θ ^ 2 :=
  Sharing.FKΘs_exchange_ii (id : Fin 4 → Fin 4) (Sharing.id_refines Sharing.pat1324) θ h0 h1

/-- `F_C(ψ_{U_θ}) = cos² θ` (`Ceilings.FCΘ`) for `0 ≤ θ ≤ π/4`. -/
theorem FCΘ_psiEx {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4) :
    Ceilings.FCΘ (Sharing.psiEx θ) = Real.cos θ ^ 2 := by
  have h := Sharing.FCΘs_exchange_ii (id : Fin 4 → Fin 4) (Sharing.id_refines Sharing.pat1324) θ h0 h1
  have hn : nsq (Θ (Sharing.psiEx θ)) ≠ 0 := by
    rw [NQubit.nsq_Θ, Sharing.nsq_psiEx]; norm_num
  unfold Sharing.FCΘs at h
  rw [FCs_id_eq _ _ hn] at h
  exact h

/-- **`thm:heis`** for the Choi probe, `0 ≤ θ ≤ π/4`: `F_C = F_K = (1+cos 2θ)/2 = cos²θ`, which is the
Weyl-side value `FKmag(dgate (θ/2,θ/2,θ/2))` of `thm:gatefk`, and
`-log F_C = C_K = log(2/(1+cos 2θ))` (calibration). -/
theorem exchange_law {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4) :
    Ceilings.FCΘ (Sharing.psiEx θ) = (1 + cos (2 * θ)) / 2 ∧
      FKΘ (Sharing.psiEx θ) = (1 + cos (2 * θ)) / 2 ∧
      FKmag (dgate (fun _ => θ / 2)) = (1 + cos (2 * θ)) / 2 ∧
      -Real.log (Ceilings.FCΘ (Sharing.psiEx θ)) = CKex (cos (2 * θ)) ∧
      CK (Sharing.psiEx θ) = CKex (cos (2 * θ)) := by
  have hcos : Real.cos θ ^ 2 = (1 + cos (2 * θ)) / 2 := by
    rw [Real.cos_sq θ]; ring
  have hc0 : 0 ≤ cos (2 * θ) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hF : FKmag (dgate (fun _ => θ / 2)) = (1 + cos (2 * θ)) / 2 := by
    rw [FKmag_gate_exchange, abs_of_nonneg hc0]
  have e : ∀ F : ℝ, F = (1 + cos (2 * θ)) / 2 → -Real.log F = CKex (cos (2 * θ)) := by
    intro F hF'
    unfold CKex
    rw [hF', ← Real.log_inv, inv_div]
  have hfc : Ceilings.FCΘ (Sharing.psiEx θ) = (1 + cos (2 * θ)) / 2 := by
    rw [FCΘ_psiEx h0 h1, hcos]
  have hfk : FKΘ (Sharing.psiEx θ) = (1 + cos (2 * θ)) / 2 := by
    rw [FKΘ_psiEx h0 h1, hcos]
  exact ⟨hfc, hfk, hF, e _ hfc, e _ hfk⟩

/-- The exchange gates form a calibrated ruler on `[0, log 2]` (`s4-reversals`): every
`r ∈ [0, log 2]` is `CKex (cos 2θ)` for some `θ ∈ [0, π/4]`. -/
theorem exchange_ruler {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ Real.log 2) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ π / 4 ∧ CKex (cos (2 * θ)) = r := by
  have he : Real.exp r ≤ 2 := by
    calc Real.exp r ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 h1
      _ = 2 := Real.exp_log (by norm_num)
  have he1 : 1 ≤ Real.exp r := Real.one_le_exp h0
  set s : ℝ := 2 / Real.exp r - 1 with hs
  have hpos := Real.exp_pos r
  have hs1 : s ≤ 1 := by
    rw [hs]; have : 2 / Real.exp r ≤ 2 := by rw [div_le_iff₀ hpos]; nlinarith
    linarith
  have hs0 : 0 ≤ s := by
    rw [hs]; have : 1 ≤ 2 / Real.exp r := by rw [le_div_iff₀ hpos]; linarith
    linarith
  refine ⟨Real.arccos s / 2, by have := Real.arccos_nonneg s; linarith, ?_, ?_⟩
  · have : Real.arccos s ≤ π / 2 := Real.arccos_le_pi_div_two.2 hs0
    linarith
  · rw [show 2 * (Real.arccos s / 2) = Real.arccos s by ring, Real.cos_arccos (by linarith) hs1]
    unfold CKex
    rw [show 1 + s = 2 / Real.exp r by rw [hs]; ring,
      show (2:ℝ) / (2 / Real.exp r) = Real.exp r by field_simp]
    exact Real.log_exp r



/-! ### The region and the ruler together -/

/-- The envelope hypothesis at `U_*` follows from the envelope bound for all `u ≥ 1`. -/
theorem EnvelopeAtStar_of_forall {ξ : ℝ}
    (h : ∀ u : ℝ, 1 ≤ u → rlf (cos (2 * cStar 2)) (cos (2 * cStar 1)) u ≤ exp (-ξ)) :
    EnvelopeAtStar ξ := by
  have := h (137 / 100) (by norm_num)
  rw [cStar_two, cStar_one, show 2 * (8 / 25 : ℝ) = 16 / 25 by norm_num,
    show 2 * (19 / 50 : ℝ) = 19 / 25 by norm_num] at this
  exact this

/-- **`thm:ratefailregion`, reversals** (`s4-reversals`): for a gate in the region with (R3), if
the exponent `ξ ≥ 0` obeys the envelope bound for all `u ≥ 1` and `C_K ≤ log 2`, then there is an
exchange gate `θ ∈ [0, π/4]` forming a strict reversal with it (an open interval of comparators). -/
theorem region_reversal (c : Fin 3 → ℝ) (h0 : 0 < |c 2|) (h1 : |c 2| < c 1) (h2 : c 1 < c 0)
    (h3 : c 0 + |c 2| < π / 4) (hR3 : cos (4 * c 2) < cos (2 * c 1) * cos (2 * c 2)) {ξ : ℝ}
    (hξ0 : 0 ≤ ξ)
    (hξ : ∀ u : ℝ, 1 ≤ u → rlf (cos (2 * c 2)) (cos (2 * c 1)) u ≤ exp (-ξ))
    (hC : CKg c ≤ Real.log 2) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ π / 4 ∧
      StrictReversal (CKg c) ξ (CKex (cos (2 * θ))) (CKex (cos (2 * θ))) := by
  have hgap := (region_gap c h0 h1 h2 h3 hR3).2.2 ξ hξ
  obtain ⟨θ, t0, t1, ht⟩ := exchange_ruler (r := (ξ + CKg c) / 2) (by linarith) (by linarith)
  refine ⟨θ, t0, t1, ?_⟩
  rw [ht]
  exact reversal_of_gap_ruler hgap (by linarith) (by linarith)


/-! ### Eight qubits and blocks of four, `cor:calgeom-spin1extensive` -/

/-- `F_K(ψ_{U_{π/4}}) = F_C(ψ_{U_{π/4}}) = 1/2` (`thm:psipluskramers`; `ψ_{U_{π/4}}` is `ψ₊` up to exchanging
spins 2 and 4). -/
theorem exchange_pi4 :
    Ceilings.FCΘ (Sharing.psiEx (π / 4)) = 1 / 2 ∧ FKΘ (Sharing.psiEx (π / 4)) = 1 / 2 := by
  have h := exchange_law (θ := π / 4) (by positivity) le_rfl
  have : cos (2 * (π / 4)) = 0 := by
    rw [show 2 * (π / 4) = π / 2 by ring]; exact Real.cos_pi_div_two
  rw [this] at h
  exact ⟨by linarith [h.1], by linarith [h.2.1]⟩

/-- `Ψ_θ = M₄ ⊗ ψ_{U_θ}` (eight spins). -/
noncomputable def Psi8 (θ : ℝ) : Ψ (4 + 4) := tens Ceilings.M4v (Sharing.psiEx θ)

/-- The comparator `Φ = ψ_{U_{π/4}} ⊗ ψ_{U_{π/4}}` (the paper's `ψ₊ ⊗ ψ₊`: the Choi state of `√SWAP`
is `ψ₊` after exchanging spins 2 and 4, and `F_K`, `F_C` are invariant under this relabelling). -/
noncomputable def Phi8 : Ψ (4 + 4) := tens (Sharing.psiEx (π / 4)) (Sharing.psiEx (π / 4))

/-- **`cor:calgeom-spin1extensive` (b), values** (`0 ≤ θ ≤ π/4`, given `F_K(M₄) ≤ 4/9` [R7 for `M₄`]):
`F_K(Ψ_θ) = (4/9)(1+s)/2`, `F_C(Ψ_θ) = (1/2)(1+s)/2`, `s = cos 2θ`. -/
theorem Psi8_values (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ π / 4) :
    FKΘ (Psi8 θ) = 4 / 9 * ((1 + cos (2 * θ)) / 2) ∧
      Ceilings.FCΘ (Psi8 θ) = 1 / 2 * ((1 + cos (2 * θ)) / 2) ∧
      CK (Psi8 θ) = CK8 (cos (2 * θ)) ∧
      -Real.log (Ceilings.FCΘ (Psi8 θ)) = xi8 (cos (2 * θ)) := by
  obtain ⟨hfc, hfk, -⟩ := exchange_law h0 h1
  have e49 := Unify.FKΘ_M4v_eq_of_le h49
  have e12 := M4Support.FCΘ_M4v_eq
  have hK8 : FKΘ (Psi8 θ) = 4 / 9 * ((1 + cos (2 * θ)) / 2) := by
    unfold Psi8; rw [NQubit.FKΘ_tens, e49, hfk]
  have hC8 : Ceilings.FCΘ (Psi8 θ) = 1 / 2 * ((1 + cos (2 * θ)) / 2) := by
    unfold Psi8
    rw [Ceilings.FCΘ_tens _ _ (by rw [Ceilings.nsq_M4v]; norm_num)
      (by rw [Sharing.nsq_psiEx]; norm_num), e12, hfc]
  exact ⟨hK8, hC8, by unfold CK CK8; rw [hK8], by unfold xi8; rw [hC8]⟩

theorem Phi8_values :
    CK Phi8 = Real.log 4 ∧ -Real.log (Ceilings.FCΘ Phi8) = Real.log 4 := by
  obtain ⟨hc, hk⟩ := exchange_pi4
  have e : ∀ F : ℝ, F = 1 / 4 → -Real.log F = Real.log 4 := by
    intro F hF; rw [hF, ← Real.log_inv]; norm_num
  have hk8 : FKΘ Phi8 = 1 / 4 := by unfold Phi8; rw [NQubit.FKΘ_tens, hk]; norm_num
  have hc8 : Ceilings.FCΘ Phi8 = 1 / 4 := by
    unfold Phi8
    rw [Ceilings.FCΘ_tens _ _ (by rw [Sharing.nsq_psiEx]; norm_num)
      (by rw [Sharing.nsq_psiEx]; norm_num), hc]; norm_num
  exact ⟨e _ hk8, e _ hc8⟩

/-- **`cor:calgeom-spin1extensive` (b)**: for `0 < s = cos 2θ < 1/8` the pair `(Ψ_θ, Φ)` is a strict
reversal, with `C_K(Ψ) = log (9/(2(1+s)))`, `-log F_C(Ψ) = log (4/(1+s))`.  (Here `-log F_C` stands in
for `ξ_inv`; the equality `ξ_inv = -log F_C` for both factors is the recalled `thm:expceiling` input.) -/
theorem eight_qubit_reversal (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4) (hs0 : 0 < cos (2 * θ)) (hs1 : cos (2 * θ) < 1 / 8) :
    StrictReversal (CK (Psi8 θ)) (-Real.log (Ceilings.FCΘ (Psi8 θ))) (CK Phi8)
        (-Real.log (Ceilings.FCΘ Phi8)) ∧
      CK (Psi8 θ) = Real.log (9 / (2 * (1 + cos (2 * θ)))) ∧
      -Real.log (Ceilings.FCΘ (Psi8 θ)) = Real.log (4 / (1 + cos (2 * θ))) := by
  obtain ⟨-, -, hck, hxi⟩ := Psi8_values h49 h0 h1
  obtain ⟨hp1, hp2⟩ := Phi8_values
  rw [hck, hxi, hp1, hp2]
  exact ⟨⟨(CK8_gt_iff _ hs0.le).2 hs1, (xi8_lt_iff _ hs0.le).2 hs0⟩, CK8_eq _ hs0.le,
    xi8_eq _ hs0.le⟩

/-- Arithmetic of (b): advantage and deficit add to `log (9/8)` (`Arithmetic.advantage_deficit`). -/
theorem eight_qubit_budget {s : ℝ} (hs : 0 ≤ s) :
    (CK8 s - Real.log 4) + (Real.log 4 - xi8 s) = Real.log (9 / 8) := advantage_deficit s hs

/-- **`cor:calgeom-spin1extensive` (a), values** (`F_K(M₄) ≤ 4/9`): for `n = 4(m+1)` spins,
`C_K(M₄^{⊗(m+1)}) = (m+1) log (9/4)`, `-log F_C(M₄^{⊗(m+1)}) = (m+1) log 2`, and the difference is
`(m+1) log (9/8) = (n/4) log (9/8)`, growing linearly. -/
theorem blocks_gap (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) (m : ℕ) :
    CK (Ceilings.M4pow m) = (m + 1) * Real.log (9 / 4) ∧
      -Real.log (Ceilings.FCΘ (Ceilings.M4pow m)) = (m + 1) * Real.log 2 ∧
      CK (Ceilings.M4pow m) - -Real.log (Ceilings.FCΘ (Ceilings.M4pow m)) =
        (m + 1) * Real.log (9 / 8) := by
  have e49 := Unify.FKΘ_M4v_eq_of_le h49
  have hc := (Ceilings.CK_M4pow e49 m).2
  have hw := (M4Support.M4pow_window_of_h49 e49 m).1
  refine ⟨hc, hw, ?_⟩
  rw [hc, hw]
  have : Real.log (9 / 4) - Real.log 2 = Real.log (9 / 8) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  linear_combination ((m : ℝ) + 1) * this


/-! ### Tensorisation arithmetic, `thm:calgeom-tensorisation`

The Helstrom-error inequality `P_⊗ ≥ ½ ∏ P_i` is not formalised.  What is formalised is what the proof of the paper uses after those
inputs: the product inequality `∏(aᵢ + bᵢ) ≥ ∏ aᵢ + ∏ bᵢ`, the harmonic-product consequence, and the
passage from `P_Ψ(k) ≥ ½ ∏ P_i(k)` to the sum of upper rates. -/

/-- `∏ aᵢ + ∏ bᵢ ≤ ∏ (aᵢ + bᵢ)` for nonnegative numbers over a nonempty index set. -/
theorem prod_add_le {ι : Type*} (s : Finset ι) (hne : s.Nonempty) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    ∏ i ∈ s, a i + ∏ i ∈ s, b i ≤ ∏ i ∈ s, (a i + b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hne (by simp)
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.prod_insert hj]
    have haj := ha j (Finset.mem_insert_self _ _)
    have hbj := hb j (Finset.mem_insert_self _ _)
    rcases t.eq_empty_or_nonempty with rfl | htne
    · simp
    have ih' := ih htne (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    have hA : 0 ≤ ∏ i ∈ t, a i := Finset.prod_nonneg fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hB : 0 ≤ ∏ i ∈ t, b i := Finset.prod_nonneg fun i hi => hb i (Finset.mem_insert_of_mem hi)
    nlinarith [mul_nonneg haj hB, mul_nonneg hbj hA, mul_le_mul_of_nonneg_left ih' (add_nonneg haj hbj)]

/-- The harmonic product: `∏ aᵢbᵢ/(aᵢ+bᵢ) ≤ ∏aᵢ ∏bᵢ/(∏aᵢ + ∏bᵢ)` for positive numbers
(the step `𝓗(⊗ρ,⊗σ) ≥ ∏ 𝓗(ρᵢ,σᵢ)` of the proof). -/
theorem prod_harmonic_le {ι : Type*} (s : Finset ι) (hne : s.Nonempty) (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i)
    (hb : ∀ i ∈ s, 0 < b i) :
    ∏ i ∈ s, (a i * b i / (a i + b i)) ≤ (∏ i ∈ s, a i) * (∏ i ∈ s, b i) / (∏ i ∈ s, a i + ∏ i ∈ s, b i) := by
  have hA : 0 < ∏ i ∈ s, a i := Finset.prod_pos ha
  have hB : 0 < ∏ i ∈ s, b i := Finset.prod_pos hb
  have hab : ∀ i ∈ s, 0 < a i + b i := fun i hi => add_pos (ha i hi) (hb i hi)
  have hC : 0 < ∏ i ∈ s, (a i + b i) := Finset.prod_pos hab
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (prod_add_le s hne a b (fun i hi => (ha i hi).le) (fun i hi => (hb i hi).le))

/-- Upper exponent rate of a sequence of errors: `limsup_k -(1/k) log P(k) ≤ r`, in `ε`-form. -/
def RateLE (P : ℕ → ℝ) (r : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, -Real.log (P k) / k ≤ r + ε

/-- **`thm:calgeom-tensorisation`, upper bound, after the input `P_Ψ(k) ≥ ½ ∏ P_i(k)`**: the upper
rate of `Ψ = ⊗ψ_i` is at most the sum of the upper rates of the factors. -/
theorem RateLE_prod_half {ι : Type*} (s : Finset ι) (P : ι → ℕ → ℝ) (Q : ℕ → ℝ) (r : ι → ℝ)
    (hP : ∀ i ∈ s, ∀ k, 0 < P i k) (hQ : ∀ k, 1 / 2 * ∏ i ∈ s, P i k ≤ Q k)
    (hr : ∀ i ∈ s, RateLE (P i) (r i)) : RateLE Q (∑ i ∈ s, r i) := by
  intro ε hε
  set n : ℝ := (s.card : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set δ : ℝ := ε / (2 * (n + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have h1 : ∀ᶠ k : ℕ in atTop, ∀ i ∈ s, -Real.log (P i k) / k ≤ r i + δ :=
    (Filter.eventually_all_finset s).2 (fun i hi => hr i hi δ hδ0)
  have h2 : ∀ᶠ k : ℕ in atTop, Real.log 2 / k ≤ ε / 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * Real.log 2 / ε)
    filter_upwards [eventually_ge_atTop (N + 1)] with k hk
    have hk' : (N : ℝ) + 1 ≤ k := by exact_mod_cast hk
    have hkp : 0 < (k : ℝ) := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    rw [div_le_iff₀ hkp]
    have := (div_lt_iff₀ hε).1 hN
    nlinarith
  filter_upwards [h1, h2, eventually_ge_atTop 1] with k hk1 hk2 hk0
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk0
  have hprod : 0 < ∏ i ∈ s, P i k := Finset.prod_pos (fun i hi => hP i hi k)
  have hlog : Real.log (1 / 2 * ∏ i ∈ s, P i k) ≤ Real.log (Q k) :=
    Real.log_le_log (by positivity) (hQ k)
  rw [Real.log_mul (by norm_num) hprod.ne', Real.log_prod (fun i hi => (hP i hi k).ne')] at hlog
  have hl2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hl2] at hlog
  have hsum : (∑ i ∈ s, -Real.log (P i k)) / k ≤ ∑ i ∈ s, (r i + δ) := by
    rw [Finset.sum_div]; exact Finset.sum_le_sum hk1
  have hsum' : ∑ i ∈ s, (r i + δ) = ∑ i ∈ s, r i + n * δ := by
    rw [Finset.sum_add_distrib]; simp [hn]
  have hnδ : n * δ ≤ ε / 2 := by
    rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hneg : -Real.log (Q k) ≤ Real.log 2 + ∑ i ∈ s, -Real.log (P i k) := by
    rw [Finset.sum_neg_distrib]; linarith
  calc -Real.log (Q k) / k ≤ (Real.log 2 + ∑ i ∈ s, -Real.log (P i k)) / k :=
        div_le_div_of_nonneg_right hneg hkpos.le
    _ = Real.log 2 / k + (∑ i ∈ s, -Real.log (P i k)) / k := add_div _ _ _
    _ ≤ ∑ i ∈ s, r i + ε := by linarith

/-- **`thm:calgeom-tensorisation`, additivity**: if the exponent `ξ` of the product lies between
`∑ -log F_C(ψ_i)` and `∑ ξ̄(ψ_i)` and `-log F_C(ψ_i) = ξ̄(ψ_i)` for every factor, then
`ξ = ∑ ξ̄(ψ_i)`. -/
theorem additive_of_tie {ι : Type*} (s : Finset ι) (L U : ι → ℝ) (ξ : ℝ) (hLU : ∀ i ∈ s, L i = U i)
    (hlo : ∑ i ∈ s, L i ≤ ξ) (hhi : ξ ≤ ∑ i ∈ s, U i) : ξ = ∑ i ∈ s, U i := by
  have : ∑ i ∈ s, L i = ∑ i ∈ s, U i := Finset.sum_congr rfl hLU
  linarith

/-- **`cor:calgeom-spin1extensive` (a), exponent**: for `M₄^{⊗(m+1)}`, if `ξ` satisfies the support lower
bound `-log F_C ≤ ξ` and the tensorised upper bound `ξ ≤ (m+1) log 2` (from `ξ̄_inv(M₄) ≤ log 2`),
then `ξ = (m+1) log 2 < C_K`, so the gap is `(m+1) log (9/8) = (n/4) log (9/8)`. -/
theorem blocks_exponent (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) (m : ℕ) (ξ : ℝ)
    (hlo : -Real.log (Ceilings.FCΘ (Ceilings.M4pow m)) ≤ ξ) (hhi : ξ ≤ (m + 1) * Real.log 2) :
    ξ = (m + 1) * Real.log 2 ∧ CK (Ceilings.M4pow m) - ξ = (m + 1) * Real.log (9 / 8) := by
  obtain ⟨hc, hw, hd⟩ := blocks_gap h49 m
  have hξ : ξ = (m + 1) * Real.log 2 := le_antisymm hhi (by rw [← hw]; exact hlo)
  refine ⟨hξ, ?_⟩
  rw [hξ, ← hw]; exact hd


/-! ### `thm:m4exponent`, `thm:expceiling`, `cor:fourdecoh`: the arithmetic around `ξ_inv`

`ξ_inv` is not defined in the repository.  Below `ξ` is an arbitrary real number standing for it, and
the hypotheses are the two inequalities the paper's proofs actually use: the support lower bound
`-log F_C ≤ ξ` (`thm:supportrate`) and an upper bound (`thm:expceiling`, or the product-branch bound). -/

theorem log_9_4_bounds : (0.81093 : ℝ) < log (9 / 4) ∧ log (9 / 4) < 0.81094 := by
  have e : (1 + 1 / 5) / (1 - 1 / 5) = (3 / 2 : ℝ) := by norm_num
  have h1 := log_ratio_ge (1 / 5) (by norm_num) (by norm_num) 5
  have h2 := log_ratio_le (1 / 5) (by norm_num) (by norm_num) 5
  rw [e] at h1 h2
  norm_num [Finset.sum_range_succ] at h1 h2
  have h : log (9 / 4 : ℝ) = 2 * log (3 / 2) := by
    rw [← Real.log_rpow (by norm_num)]; norm_num
  rw [h]
  constructor <;> linarith

/-- **`thm:m4exponent`** (`F_K(M₄) ≤ 4/9`): if `-log F_C(M₄) ≤ ξ ≤ log 2` (the upper bound is
`thm:expceiling` at the maximally mixed marginals), then `ξ = log 2 < C_K(M₄) = log (9/4)`,
`C_K - ξ = log (9/8)`, and the fraction `1 - ξ/C_K` is in `(0.1452, 0.1453)`. -/
theorem m4_exponent (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) (ξ : ℝ)
    (hlo : -Real.log (Ceilings.FCΘ Ceilings.M4v) ≤ ξ) (hhi : ξ ≤ Real.log 2) :
    ξ = Real.log 2 ∧ CK Ceilings.M4v = Real.log (9 / 4) ∧ ξ < CK Ceilings.M4v ∧
      CK Ceilings.M4v - ξ = Real.log (9 / 8) ∧
      0.1452 < 1 - ξ / CK Ceilings.M4v ∧ 1 - ξ / CK Ceilings.M4v < 0.1453 := by
  have e49 := Unify.FKΘ_M4v_eq_of_le h49
  have hCK : CK Ceilings.M4v = Real.log (9 / 4) := by
    have h : CK Ceilings.M4v = (((0 : ℕ) : ℝ) + 1) * Real.log (9 / 4) :=
      (Ceilings.CK_M4pow e49 0).2
    rw [h]; norm_num
  have hF : Ceilings.FCΘ Ceilings.M4v = 1 / 2 := M4Support.FCΘ_M4v_eq
  have hξ : ξ = Real.log 2 := by
    refine le_antisymm hhi ?_
    have : -Real.log (Ceilings.FCΘ Ceilings.M4v) = Real.log 2 := by
      rw [hF, one_div, Real.log_inv, neg_neg]
    linarith
  have hl : Real.log 2 < Real.log (9 / 4) := Real.log_lt_log (by norm_num) (by norm_num)
  have hd : Real.log (9 / 4) - Real.log 2 = Real.log (9 / 8) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  obtain ⟨a1, a2⟩ := log_9_4_bounds
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  rw [hCK, hξ]
  have hApos : 0 < Real.log (9 / 4) := by linarith
  refine ⟨rfl, rfl, hl, hd, ?_, ?_⟩
  · have : Real.log 2 / Real.log (9 / 4) < 0.8548 := by
      rw [div_lt_iff₀ hApos]; linarith
    linarith
  · have : 0.8547 < Real.log 2 / Real.log (9 / 4) := by
      rw [lt_div_iff₀ hApos]; linarith
    linarith

/-- **`thm:expceiling`, arithmetic**: with a maximally mixed qubit the bound
`log (λmax/λmin²)` is `log 2`; for `0 < m ≤ 1/2` it is at least `log 2`, with equality only at `m = 1/2`. -/
theorem expceiling_arith :
    Real.log ((1 / 2) / (1 / 2) ^ 2) = Real.log 2 ∧
      ∀ m : ℝ, 0 < m → m ≤ 1 / 2 → Real.log 2 ≤ Real.log ((1 - m) / m ^ 2) := by
  refine ⟨by norm_num, fun m hm hm2 => ?_⟩
  refine Real.log_le_log (by norm_num) ?_
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- A critical state with `F_C = 1/2` has `ξ = log 2` (`thm:expceiling`, last sentence), given the two
bounds. -/
theorem critical_exponent {F ξ : ℝ} (hF : F = 1 / 2) (hlo : -Real.log F ≤ ξ) (hhi : ξ ≤ Real.log 2) :
    ξ = Real.log 2 := by
  refine le_antisymm hhi ?_
  rw [hF, one_div, Real.log_inv, neg_neg] at hlo
  exact hlo

/-- **`cor:fourdecoh`, glue**: from the two product-branch bounds `e^{-ξ} ≥ 1 - p` (achiral branch) and
`e^{-ξ} ≥ φ p` (top branch, three-qubit floor `φ`), `ξ ≤ log (1 + 1/φ)`. -/
theorem fourdecoh_glue {φ p ξ : ℝ} (hφ : 0 < φ) (h1 : 1 - p ≤ Real.exp (-ξ))
    (h2 : φ * p ≤ Real.exp (-ξ)) : ξ ≤ Real.log (1 + 1 / φ) := by
  have hb : φ / (1 + φ) ≤ Real.exp (-ξ) := le_trans (max_branch_bound φ p hφ) (max_le h1 h2)
  have hpos : 0 < φ / (1 + φ) := by positivity
  have hl := Real.log_le_log hpos hb
  rw [Real.log_exp] at hl
  have : φ / (1 + φ) = (1 + 1 / φ)⁻¹ := by field_simp; ring
  rw [this, Real.log_inv] at hl
  linarith

/-- `x = 1/(1+2φ)` turns `1 + 1/φ` into `(1+x)/(1-x)`: the atanh enclosure of `log (1 + 1/φ)`. -/
theorem log_one_add_inv_le (φ : ℝ) (hφ : 0 < φ) (n : ℕ) :
    Real.log (1 + 1 / φ) ≤ 2 * ∑ i ∈ Finset.range n, (1 / (1 + 2 * φ)) ^ (2 * i + 1) / (2 * i + 1) +
      2 * ((1 / (1 + 2 * φ)) ^ (2 * n + 1) / (1 - (1 / (1 + 2 * φ)) ^ 2)) := by
  have hx0 : 0 ≤ 1 / (1 + 2 * φ) := by positivity
  have hx1 : 1 / (1 + 2 * φ) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have e : (1 + 1 / (1 + 2 * φ)) / (1 - 1 / (1 + 2 * φ)) = 1 + 1 / φ := by
    field_simp; ring
  have := log_ratio_le _ hx0 hx1 n
  rwa [e] at this

theorem log_365_169_lt : Real.log (1 + 1 / (169 / 196 : ℝ)) < 0.77 := by
  have h := log_one_add_inv_le (169 / 196) (by norm_num) 8
  refine lt_of_le_of_lt h ?_
  norm_num [Finset.sum_range_succ]

/-- **`cor:fourdecoh`**: with the analytic three-qubit floor `169/196`, `ξ ≤ log (365/169) < 0.77`. -/
theorem fourdecoh_value {p ξ : ℝ} (h1 : 1 - p ≤ Real.exp (-ξ)) (h2 : 169 / 196 * p ≤ Real.exp (-ξ)) :
    ξ ≤ Real.log (365 / 169) ∧ ξ < 0.77 := by
  have h := fourdecoh_glue (by norm_num : (0 : ℝ) < 169 / 196) h1 h2
  have e : (1 + 1 / (169 / 196 : ℝ)) = 365 / 169 := by norm_num
  rw [e] at h
  exact ⟨h, lt_of_le_of_lt h (by rw [← e]; exact log_365_169_lt)⟩

theorem log_floor_certified_lt {φ : ℝ} (hφ : 0.897354554944 ≤ φ) :
    Real.log (1 + 1 / φ) < 0.748766 := by
  have hp : 0 < φ := lt_of_lt_of_le (by norm_num) hφ
  have hm : Real.log (1 + 1 / φ) ≤ Real.log (1 + 1 / (0.897354554944 : ℝ)) :=
    Real.log_le_log (by positivity) (by gcongr)
  refine lt_of_le_of_lt hm (lt_of_le_of_lt (log_one_add_inv_le _ (by norm_num) 8) ?_)
  norm_num [Finset.sum_range_succ]

/-- **`cor:fourgapfloor`, arithmetic** (the floor `φ ≥ 0.897354554944 = (0.947288)²` is the
computer-assisted `thm:threequbitminimiser`, recalled): `ξ < 0.748766`. -/
theorem fourgapfloor_arith {φ p ξ : ℝ} (hφ : 0.897354554944 ≤ φ) (h1 : 1 - p ≤ Real.exp (-ξ))
    (h2 : φ * p ≤ Real.exp (-ξ)) : ξ < 0.748766 :=
  lt_of_le_of_lt (fourdecoh_glue (lt_of_lt_of_le (by norm_num) hφ) h1 h2)
    (log_floor_certified_lt hφ)


end FormalResearch.FrameFree.Reversals
