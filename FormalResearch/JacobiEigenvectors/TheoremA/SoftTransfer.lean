module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.SoftParabolicCylinder
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftOverlap
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftWeights

/-!
# Paper J, Layer 2 (L2.C6): the transfer condition (S3) of the soft-edge chain is derived (finding F-W2-7 resolved)

Source: Paper J `app_thmA.tex` "The soft edges: proof of Proposition prop:tha-W2", Steps 2--3 (the forbidden overlap bond `j_1`, the switch bond `j_2` with `(v~, -u~) = (u_-, v_-) M_-(a) S`);
`engine.tex` after `thm:eng-volterra` (cases (i), (ii) of (S3)).

## Proved here

* geometry of the coordinate: `zeta_mvt` (`d_- (x_2 - x_1) <= zeta(x_2) - zeta(x_1) <= d_+ (x_2 - x_1)` on `|x| <= 2 eta`), `muTilde` bounds, `Zq_lb` (`zeta^2/4 - mu~ >= c_{z1}/8` away from the fold: the Liouville--Green margin `k_2 >= c/h`).
* `Mbal_le_of`, `Mbal_prod_le`: `M_bal M_bal <= C_M h^{1/2}` at `j_1` (Weber `M` at `j_1`, PC `M` at `j_1 + 1`) from `Y_forb` and `zeta_far`.
* `softGap`, the constants `softLamC` (the explicit `Lambda`) and `softH1` (smallness of `h`).
* `soft_transfer`: **for every `lam` with `((chain).rescale1 lam).PreValid`, the rescaled chain satisfies the full engine hypotheses `Valid` for the constants `{cs with Lambda := softLamC}`**: (S3) at `j_1` by `PreValid.transferAt_forbidden`
  (`A_{j_1} > 0` from the Casoratian bound and `0 <= bondA`, `bondA_le`, the one-step comparison `Eminus_ratio` of the weights, the margin `k_2 >= c/h` at `j_1, j_1+1`), (S3) at `j_2` by `TransferAtΛ_of_linear` and `pcSwap_eq_pcMinus`
  (`M_-(a) S`, `|Z_{j_2}| <= d_+ h^{1/2}`, `exp(-Z^2/4) <= E_- <= 1`).

## Differences from the paper

* `Lambda` is the explicit constant `softLamC = max(cs.Λ, tΛ1, 2)`, where `cs.Λ` and `tΛ1` depend on `(K_A, K_B, K_w, c_-, C_E, C_A, C_M, C_w)`.  The number `2.26` of the paper is not a bound on this `Λ`: it is the operator-norm bound `‖M_-(a)‖_op ≤ 1 + √(π/2) < 2.26` of `charts.tex` (entries at most `√(π/2) < 2`, which the constant `2` dominates entrywise).
* The soft chart now carries `bondA_le` (`a_n <= C_A`) and `muS_bd` for `r = 0` as fields (they are used implicitly by the paper); (S3) is no longer a field.

## Not formalised

Nothing beyond what the docstring of `Charts/SoftParabolicCylinder.lean` lists.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Engine

/-! ### Bounds for `M_bal` -/

/-- `M_bal(a,z) <= K^{-1/4}` if `K <= |z^2/4 + a|`, `K > 0`. -/
lemma Mbal_le_of (a z : ℝ) {K : ℝ} (hK : 0 < K) (h : K ≤ |z ^ 2 / 4 + a|) : Mbal a z ≤ K ^ (-(1 : ℝ) / 4) := by
  unfold Mbal
  have h1 : K ≤ k2 a z := le_trans h (le_max_left _ _)
  exact Real.rpow_le_rpow_of_nonpos hK h1 (by norm_num)

lemma Mbal_pos (a z : ℝ) : 0 < Mbal a z := by
  unfold Mbal k2
  apply Real.rpow_pos_of_pos
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _) (le_max_right _ _)

/-- `M_bal(a,z) M_bal(a',z') <= (K K')^{-1/4}` for `K <= |z^2/4 + a|`, `K' <= |z'^2/4 + a'|`; with `K = c/h`, `K' = c'/h`:
`<= (c c')^{-1/4} h^{1/2}`. -/
lemma Mbal_prod_le (a z a' z' c c' h : ℝ) (hc : 0 < c) (hc' : 0 < c') (hh : 0 < h) (h1 : c / h ≤ |z ^ 2 / 4 + a|)
    (h2 : c' / h ≤ |z' ^ 2 / 4 + a'|) : Mbal a z * Mbal a' z' ≤ (c * c') ^ (-(1 : ℝ) / 4) * Real.sqrt h := by
  have e1 := Mbal_le_of a z (by positivity) h1
  have e2 := Mbal_le_of a' z' (by positivity) h2
  have hp1 := Mbal_pos a z
  have hp2 := Mbal_pos a' z'
  calc Mbal a z * Mbal a' z' ≤ (c / h) ^ (-(1 : ℝ) / 4) * (c' / h) ^ (-(1 : ℝ) / 4) :=
        mul_le_mul e1 e2 hp2.le (by positivity)
    _ = ((c / h) * (c' / h)) ^ (-(1 : ℝ) / 4) := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
    _ = (c * c') ^ (-(1 : ℝ) / 4) * Real.sqrt h := by
        have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
        have key : ((Real.sqrt h ^ 4)⁻¹) ^ (-(1 : ℝ) / 4) = Real.sqrt h := by
          rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast (Real.sqrt h) 4, ← Real.rpow_mul hs.le]
          have : ((4 : ℕ) : ℝ) * (-(1 : ℝ) / 4) = -1 := by norm_num
          rw [this, Real.rpow_neg_one, inv_inv]
        have hs4 : Real.sqrt h ^ 4 = h ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hh.le]
        have e : (c / h) * (c' / h) = (c * c') * (Real.sqrt h ^ 4)⁻¹ := by
          rw [hs4]; field_simp
        rw [e, Real.mul_rpow (by positivity) (by positivity), key]

lemma bondA_nonneg' {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ) (k : ℤ) : 0 ≤ F.bondA μ N k := by
  unfold SymbolFamily.bondA
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_rfl

lemma div_div_self_eq (E m : ℝ) (hE : E ≠ 0) : E / (E / m) = m := by
  rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ hE]

namespace SoftEdgeChart

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart F P m q U V Lm)

lemma step_pos (N : ℕ) : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N

/-- `mu~ = mu_0 + sum_{r=1}^{q/2} h^{2r} mu_{2r}` so that `a = -mu~/h`. -/
def muTilde (μ : Par) (X : ℝ) (N : ℕ) : ℝ :=
  C.muS 0 μ (F.bandHi μ - X) + ∑ r ∈ Finset.Icc 1 (q / 2), F.step N ^ (2 * r) * C.muS r μ (F.bandHi μ - X)

lemma aOf_eq (μ : Par) (X : ℝ) (N : ℕ) : C.aOf μ X N = -(1 / F.step N) * C.muTilde μ X N := rfl

lemma Zof_eq (μ : Par) (X : ℝ) (N : ℕ) (n : ℤ) :
    C.Zof μ X N n = C.zeta μ (F.bandHi μ - X) (uNode (F.step N) n - C.uc μ) / Real.sqrt (F.step N) := rfl

lemma abs_alpha_le {μ : Par} {X : ℝ} (hX : |X - F.bandHi μ| ≤ C.δ0) : |F.bandHi μ - X| ≤ C.δ0 := by
  rw [abs_sub_comm]; exact hX

lemma muTilde_sub_le {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : |X - F.bandHi μ| ≤ C.δ0) {N : ℕ} (hh1 : F.step N ≤ 1) :
    |C.muTilde μ X N - C.muS 0 μ (F.bandHi μ - X)| ≤ ((q / 2 : ℕ) : ℝ) * C.Cmu * F.step N := by
  have hh := step_pos (F := F) N
  have hα := C.abs_alpha_le hX
  unfold muTilde
  rw [add_sub_cancel_left]
  have hterm : ∀ r ∈ Finset.Icc 1 (q / 2), |F.step N ^ (2 * r) * C.muS r μ (F.bandHi μ - X)| ≤ F.step N * C.Cmu := by
    intro r hr
    have hr1 := (Finset.mem_Icc.mp hr).1
    rw [abs_mul, abs_of_nonneg (pow_nonneg hh.le _)]
    have h1 : F.step N ^ (2 * r) ≤ F.step N := pow_le_of_le_one hh.le hh1 (by omega)
    have h2 : |C.muS r μ (F.bandHi μ - X)| ≤ C.Cmu := C.muS_bd r (Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hr).2⟩) μ hμ _ hα
    exact mul_le_mul h1 h2 (abs_nonneg _) hh.le
  calc |∑ r ∈ Finset.Icc 1 (q / 2), F.step N ^ (2 * r) * C.muS r μ (F.bandHi μ - X)|
      ≤ ∑ r ∈ Finset.Icc 1 (q / 2), |F.step N ^ (2 * r) * C.muS r μ (F.bandHi μ - X)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Finset.Icc 1 (q / 2), F.step N * C.Cmu := Finset.sum_le_sum hterm
    _ = ((q / 2 : ℕ) : ℝ) * C.Cmu * F.step N := by
      rw [Finset.sum_const, Nat.card_Icc]; simp; ring

lemma muS0_le {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : |X - F.bandHi μ| ≤ C.δ0) :
    |C.muS 0 μ (F.bandHi μ - X)| ≤ C.Cmu :=
  C.muS_bd 0 (Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩) μ hμ _ (C.abs_alpha_le hX)

lemma muTilde_abs_le {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : |X - F.bandHi μ| ≤ C.δ0) {N : ℕ} (hh1 : F.step N ≤ 1) :
    |C.muTilde μ X N| ≤ C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)) := by
  have h1 := C.muTilde_sub_le hμ hX hh1
  have h2 := C.muS0_le hμ hX
  have hh := step_pos (F := F) N
  have hc : 0 ≤ C.Cmu := C.consts_pos2.1
  have h3 : ((q / 2 : ℕ) : ℝ) * C.Cmu * F.step N ≤ ((q / 2 : ℕ) : ℝ) * C.Cmu := by
    have : 0 ≤ ((q / 2 : ℕ) : ℝ) * C.Cmu := by positivity
    nlinarith
  have h4 : |C.muTilde μ X N| ≤ |C.muTilde μ X N - C.muS 0 μ (F.bandHi μ - X)| + |C.muS 0 μ (F.bandHi μ - X)| := by
    calc |C.muTilde μ X N| = |(C.muTilde μ X N - C.muS 0 μ (F.bandHi μ - X)) + C.muS 0 μ (F.bandHi μ - X)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  nlinarith

/-- the smallness threshold of the transfer derivation. -/
def softH1 : ℝ :=
  min (C.η / 2) (min 1 (min (C.cz1 / (8 * (((q / 2 : ℕ) : ℝ) * C.Cmu + 1))) (1 / C.dp ^ 2)))

lemma softH1_pos : 0 < C.softH1 := by
  obtain ⟨-, hη, hdm, hdmp, -⟩ := C.consts_pos
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hz := C.consts_pos2.2
  have hc := C.consts_pos2.1
  unfold softH1
  refine lt_min (by positivity) (lt_min one_pos (lt_min ?_ (by positivity)))
  have : 0 < 8 * (((q / 2 : ℕ) : ℝ) * C.Cmu + 1) := by positivity
  positivity

lemma softH1_le_eta : C.softH1 ≤ C.η / 2 := min_le_left _ _

lemma softH1_le_one : C.softH1 ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)

lemma softH1_le_cz : C.softH1 ≤ C.cz1 / (8 * (((q / 2 : ℕ) : ℝ) * C.Cmu + 1)) :=
  le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))

lemma softH1_le_dp : C.softH1 ≤ 1 / C.dp ^ 2 :=
  le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))

/-- `(q/2) C_mu h <= c_{z1}/8` for `h <= h_1`. -/
lemma muTilde_small {N : ℕ} (hh : F.step N ≤ C.softH1) : ((q / 2 : ℕ) : ℝ) * C.Cmu * F.step N ≤ C.cz1 / 8 := by
  have hz := C.consts_pos2.2
  have hc := C.consts_pos2.1
  have hq : 0 ≤ ((q / 2 : ℕ) : ℝ) * C.Cmu := by positivity
  have h1 := le_trans hh (C.softH1_le_cz)
  have hpos : 0 < 8 * (((q / 2 : ℕ) : ℝ) * C.Cmu + 1) := by positivity
  rw [le_div_iff₀ hpos] at h1
  nlinarith

/-- `zeta` is differentiable on `|x| <= 2 eta` and satisfies the mean-value inequalities. -/
lemma zeta_mvt {μ : Par} (hμ : μ ∈ P) {α : ℝ} (hα : |α| ≤ C.δ0) {x1 x2 : ℝ} (h1 : -(2 * C.η) ≤ x1) (h12 : x1 ≤ x2)
    (h2 : x2 ≤ 2 * C.η) :
    C.dm * (x2 - x1) ≤ C.zeta μ α x2 - C.zeta μ α x1 ∧ C.zeta μ α x2 - C.zeta μ α x1 ≤ C.dp * (x2 - x1) := by
  have hd : ∀ x ∈ Set.Icc x1 x2, DifferentiableAt ℝ (C.zeta μ α) x := by
    intro x hx
    have hxb : |x| ≤ 2 * C.η := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    have := (C.zeta_deriv μ hμ α hα x hxb).1
    apply differentiableAt_of_deriv_ne_zero
    have : 0 < deriv (C.zeta μ α) x := lt_of_lt_of_le C.consts_pos.2.2.1 this
    exact this.ne'
  have hcont : ContinuousOn (C.zeta μ α) (Set.Icc x1 x2) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (C.zeta μ α) (interior (Set.Icc x1 x2)) :=
    fun x hx => (hd x (interior_subset hx)).differentiableWithinAt
  constructor
  · apply Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc x1 x2) hcont hdiff
    · intro x hx
      rw [interior_Icc] at hx
      exact (C.zeta_deriv μ hμ α hα x (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])).1
    · exact Set.left_mem_Icc.mpr h12
    · exact Set.right_mem_Icc.mpr h12
    · exact h12
  · apply Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc x1 x2) hcont hdiff
    · intro x hx
      rw [interior_Icc] at hx
      exact (C.zeta_deriv μ hμ α hα x (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])).2
    · exact Set.left_mem_Icc.mpr h12
    · exact Set.right_mem_Icc.mpr h12
    · exact h12

/-- The Liouville--Green margin: `zeta(x)^2/4 - mu~ >= c_{z1}/8` for `eta/4 <= |x| <= 2 eta` (`zeta_far`, `mu~ = mu_0 + O(h)`). -/
lemma Zq_lb {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : |X - F.bandHi μ| ≤ C.δ0) {N : ℕ} (hh : F.step N ≤ C.softH1) {x : ℝ}
    (hx1 : C.η / 4 ≤ |x|) (hx2 : |x| ≤ 2 * C.η) :
    C.cz1 / 8 ≤ C.zeta μ (F.bandHi μ - X) x ^ 2 / 4 - C.muTilde μ X N := by
  have hz := C.zeta_far μ hμ _ (C.abs_alpha_le hX) x hx2 hx1
  have hsub := C.muTilde_sub_le hμ hX (le_trans hh C.softH1_le_one)
  have hsm := C.muTilde_small hh
  have hm0 : C.muS 0 μ (F.bandHi μ - X) ≤ max (C.muS 0 μ (F.bandHi μ - X)) 0 := le_max_left _ _
  have habs := (abs_le.mp hsub).2
  nlinarith

/-- `Z^2/4 + a = (zeta^2/4 - mu~)/h`. -/
lemma Z2_add_a (μ : Par) (X : ℝ) (N : ℕ) (n : ℤ) :
    C.Zof μ X N n ^ 2 / 4 + C.aOf μ X N
      = (C.zeta μ (F.bandHi μ - X) (uNode (F.step N) n - C.uc μ) ^ 2 / 4 - C.muTilde μ X N) / F.step N := by
  have hh := step_pos (F := F) N
  rw [Zof_eq, aOf_eq, div_pow, Real.sq_sqrt hh.le]
  field_simp
  ring

/-! ### The explicit constants of the derived (S3) -/

/-- `K = (K_A + K_B) K_w`. -/
def tK : ℝ := (C.cs.KA + C.cs.KB) * C.cs.Kw

/-- `C_M`: `M_bal M_bal <= C_M h^{1/2}` at `j_1, j_1 + 1` (Weber margin `c_F/4`, PC margin `c_{z1}/8`). -/
def tCM : ℝ := (C.cF / 4 * (C.cz1 / 8)) ^ (-(1 : ℝ) / 4)

/-- `C_omega = C_A C_M`: `A M M <= C_omega omega_*`. -/
def tCω : ℝ := C.CA * C.tCM

/-- the one-step exponent of the PC weight, `D_w = d_+ ((c_Z delta_0 + 2 d_+ eta)/2 + sqrt(C_mu (1 + q/2)))`. -/
def tDw : ℝ := C.dp * ((C.cZ * C.δ0 + 2 * C.dp * C.η) / 2 + Real.sqrt (C.Cmu * (1 + ((q / 2 : ℕ) : ℝ))))

/-- `C_w = exp(D_w)`: `E_-(Z_{j_1+1}) <= C_w E_-(Z_{j_1})`. -/
def tCw : ℝ := Real.exp C.tDw

/-- `Lambda` of the forbidden overlap. -/
def tΛ1 : ℝ := max 1 (2 * ((C.cs.KA + C.cs.KB) * C.cs.Kw) ^ 2 * max C.tCw C.cs.CE * C.tCω / C.cs.cm)

/-- **The constant `Lambda` of the derived transfer condition** (`>= Lambda_chart`, `>= 2` for `M_-(a)`, `>= Lambda_{forbidden}`). -/
def softLamC : ℝ := max C.cs.Λ (max C.tΛ1 2)

lemma softLamC_ge : 1 ≤ C.softLamC := le_trans C.cs.Λ_ge (le_max_left _ _)

lemma softLamC_ge_two : 2 ≤ C.softLamC := le_trans (le_max_right _ _) (le_max_right _ _)

lemma tΛ1_ge : 1 ≤ C.tΛ1 := le_max_left _ _

lemma tΛ1_le : C.tΛ1 ≤ C.softLamC := le_trans (le_max_left _ _) (le_max_right _ _)

/-- the engine constants with `Lambda` replaced by the derived one. -/
def csT : ChainConsts := { C.cs with Λ := C.softLamC, Λ_ge := C.softLamC_ge }

lemma uNode_mono_le {h : ℝ} (hh : 0 ≤ h) {a b : ℤ} (hab : a ≤ b) : uNode h a ≤ uNode h b := by
  unfold uNode
  have : (a : ℝ) ≤ b := by exact_mod_cast hab
  nlinarith

section Trans

variable {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : |X - F.bandHi μ| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N)
  (hh : F.step N ≤ C.softH1) {lam : ℝ}
  (hV : ((C.chain μ X N).rescale1 lam).PreValid C.cs (F.step N) m)

include hμ hX hN hh hV

/-- **The positions of the overlap bonds** (from `shape` and the chain's `jj`): `0 <= j_1 < j_2`, `j_2 + 1 <= N_R`, `P = 3`,
`x_{j_1} <= -eta < x_{j_1+1}`, `x_{j_2+1} <= 2 eta`, `zeta_{j_2} <= 0 < zeta_{j_2+1}`. -/
lemma soft_pos :
    (C.chain μ X N).P = 3 ∧ 0 ≤ (C.chain μ X N).jj 1 ∧ (C.chain μ X N).jj 1 < (C.chain μ X N).jj 2 ∧
    (C.chain μ X N).jj 2 + 1 ≤ (C.chain μ X N).NR ∧
    uNode (F.step N) ((C.chain μ X N).jj 1) - C.uc μ ≤ -C.η ∧
    -C.η < uNode (F.step N) ((C.chain μ X N).jj 1 + 1) - C.uc μ ∧
    uNode (F.step N) ((C.chain μ X N).jj 2 + 1) - C.uc μ ≤ 2 * C.η ∧
    C.zeta μ (F.bandHi μ - X) (uNode (F.step N) ((C.chain μ X N).jj 2) - C.uc μ) ≤ 0 ∧
    0 < C.zeta μ (F.bandHi μ - X) (uNode (F.step N) ((C.chain μ X N).jj 2 + 1) - C.uc μ) := by
  obtain ⟨hP3, hs0, hj1u, hj1v, hZa, hZb, hNRu, hNRv⟩ := C.shape μ hμ X hX N hN
  have hsq : 0 < Real.sqrt (F.step N) := Real.sqrt_pos.mpr (step_pos (F := F) N)
  have hP3' : ((C.chain μ X N).rescale1 lam).P = 3 := hP3
  have hj0 : 0 ≤ (C.chain μ X N).jj 1 := hV.jj_nonneg (p := 1) (by rw [hP3']; norm_num)
  have hj12 : (C.chain μ X N).jj 1 < (C.chain μ X N).jj 2 := hV.jj_mono 1 (by rw [hP3']; norm_num)
  have hj2le : (C.chain μ X N).jj 2 ≤ (C.chain μ X N).NR - 1 := hV.jj_le (p := 2) (by rw [hP3']; norm_num)
  have hu2 : uNode (F.step N) ((C.chain μ X N).jj 2 + 1) ≤ uNode (F.step N) (C.chain μ X N).NR :=
    uNode_mono_le (step_pos (F := F) N).le (by omega)
  refine ⟨hP3, hj0, hj12, by omega, by linarith, by linarith, by linarith, ?_, ?_⟩
  · by_contra hpos
    exact absurd hZa (not_le.mpr (div_pos (not_le.mp hpos) hsq))
  · by_contra hneg
    exact absurd hZb (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hsq.le))


/-- **The weight ratio at the forbidden overlap**: `W_{j_1+1} <= C_w W_{j_1}` (one-step comparison of `E_-`, `E_- = E_Web/lam` at `j_1`). -/
lemma soft_Wratio :
    (C.chain μ X N).W ((C.chain μ X N).jj 1 + 1) ≤ C.tCw * (C.chain μ X N).W ((C.chain μ X N).jj 1) := by
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hμ hX hN hh hV
  obtain ⟨-, hη, hdm, hdmp, -, hcF, -, hcZ⟩ := C.consts_pos
  have hP3' : ((C.chain μ X N).rescale1 lam).P = 3 := hP3
  set h := F.step N with hhdef
  have hh0 : 0 < h := step_pos (F := F) N
  have hh1 : h ≤ 1 := hh.trans C.softH1_le_one
  have hhη : h ≤ C.η / 2 := hh.trans C.softH1_le_eta
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh0
  have hs2 : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh0.le
  have hα := C.abs_alpha_le hX
  -- weights
  have hWj1 : (C.chain μ X N).W ((C.chain μ X N).jj 1) = Eminus (C.aOf μ X N) (C.Zof μ X N ((C.chain μ X N).jj 1)) := by
    rw [C.W1_def μ hμ X hX N hN ((C.chain μ X N).jj 1) (mem_Icc.mpr ⟨hj0, le_rfl⟩)]
    unfold softLamVal
    exact div_div_self_eq _ _ (Ewell_pos _ _).ne'
  have hWj2 : (C.chain μ X N).W ((C.chain μ X N).jj 1 + 1) = Eminus (C.aOf μ X N) (C.Zof μ X N ((C.chain μ X N).jj 1 + 1)) :=
    C.W2_def μ hμ X hX N hN ((C.chain μ X N).jj 1 + 1) (mem_Icc.mpr ⟨le_rfl, by omega⟩)
  -- the coordinate at the two rows
  have hx12 : uNode h ((C.chain μ X N).jj 1 + 1) - C.uc μ - (uNode h ((C.chain μ X N).jj 1) - C.uc μ) = h := by
    unfold uNode; push_cast; ring
  have hx1lo : -(2 * C.η) ≤ uNode h ((C.chain μ X N).jj 1) - C.uc μ := by linarith
  have hx2hi : uNode h ((C.chain μ X N).jj 1 + 1) - C.uc μ ≤ 2 * C.η := by
    have : uNode h ((C.chain μ X N).jj 1 + 1) ≤ uNode h ((C.chain μ X N).jj 2 + 1) := uNode_mono_le hh0.le (by omega)
    linarith
  have hmvt1 := C.zeta_mvt hμ hα hx1lo (by linarith) hx2hi
  rw [hx12] at hmvt1
  have hx2le : uNode h ((C.chain μ X N).jj 1 + 1) - C.uc μ ≤ uNode h ((C.chain μ X N).jj 2) - C.uc μ := by
    have : uNode h ((C.chain μ X N).jj 1 + 1) ≤ uNode h ((C.chain μ X N).jj 2) := uNode_mono_le hh0.le (by omega)
    linarith
  have hx2d : uNode h ((C.chain μ X N).jj 2) - C.uc μ ≤ 2 * C.η := by
    have : uNode h ((C.chain μ X N).jj 2) ≤ uNode h ((C.chain μ X N).jj 2 + 1) := uNode_mono_le hh0.le (by omega)
    linarith
  have hmvt2 := C.zeta_mvt hμ hα (by linarith) hx2le hx2d
  have hz2neg : C.zeta μ (F.bandHi μ - X) (uNode h ((C.chain μ X N).jj 1 + 1) - C.uc μ) ≤ 0 := by
    have := mul_nonneg hdm.le (sub_nonneg.mpr hx2le)
    linarith [hmvt2.1, hza]
  have hz12 : C.zeta μ (F.bandHi μ - X) (uNode h ((C.chain μ X N).jj 1) - C.uc μ) ≤ C.zeta μ (F.bandHi μ - X) (uNode h ((C.chain μ X N).jj 1 + 1) - C.uc μ) := by
    have := mul_nonneg hdm.le hh0.le
    linarith [hmvt1.1]
  -- Z comparisons
  have hZ12 : C.Zof μ X N ((C.chain μ X N).jj 1) ≤ C.Zof μ X N ((C.chain μ X N).jj 1 + 1) := by
    rw [Zof_eq, Zof_eq]; exact div_le_div_of_nonneg_right hz12 hs.le
  have hZ2 : C.Zof μ X N ((C.chain μ X N).jj 1 + 1) ≤ 0 := by
    rw [Zof_eq]; exact div_nonpos_of_nonpos_of_nonneg hz2neg hs.le
  -- bound for zeta at x1
  have hz0 : |C.zeta μ (F.bandHi μ - X) 0| ≤ C.cZ * C.δ0 := by
    have := C.zeta_alpha μ hμ _ hα
    have h2 : C.cZ * |F.bandHi μ - X| ≤ C.cZ * C.δ0 := mul_le_mul_of_nonneg_left hα hcZ.le
    linarith
  have hmvt0 := C.zeta_mvt hμ hα hx1lo (by linarith : uNode h ((C.chain μ X N).jj 1) - C.uc μ ≤ 0) (by linarith : (0 : ℝ) ≤ 2 * C.η)
  have hzb1 : |C.zeta μ (F.bandHi μ - X) (uNode h ((C.chain μ X N).jj 1) - C.uc μ)| ≤ C.cZ * C.δ0 + 2 * C.dp * C.η := by
    have h1 := abs_le.mp hz0
    have h2 : C.dp * (0 - (uNode h ((C.chain μ X N).jj 1) - C.uc μ)) ≤ C.dp * (2 * C.η) :=
      mul_le_mul_of_nonneg_left (by linarith) hdp.le
    have hn := mul_nonneg hdm.le (by linarith : (0 : ℝ) ≤ 0 - (uNode h ((C.chain μ X N).jj 1) - C.uc μ))
    rw [abs_le]
    constructor <;> linarith [hmvt0.1, hmvt0.2]
  -- exponent of the one-step comparison
  have hdiffZ : C.Zof μ X N ((C.chain μ X N).jj 1 + 1) - C.Zof μ X N ((C.chain μ X N).jj 1) ≤ C.dp * Real.sqrt h := by
    rw [Zof_eq, Zof_eq, ← sub_div, div_le_iff₀ hs]
    have : C.dp * Real.sqrt h * Real.sqrt h = C.dp * h := by rw [mul_assoc, ← sq, hs2]
    rw [this]; exact hmvt1.2
  have hdiffZ0 : 0 ≤ C.zeta μ (F.bandHi μ - X) (uNode h ((C.chain μ X N).jj 1 + 1) - C.uc μ) / Real.sqrt h
      - C.zeta μ (F.bandHi μ - X) (uNode h ((C.chain μ X N).jj 1) - C.uc μ) / Real.sqrt h := by
    rw [← sub_div]; exact div_nonneg (sub_nonneg.mpr hz12) hs.le
  have hZ1abs : |C.Zof μ X N ((C.chain μ X N).jj 1)| ≤ (C.cZ * C.δ0 + 2 * C.dp * C.η) / Real.sqrt h := by
    rw [Zof_eq, abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right hzb1 hs.le
  have hamax : Real.sqrt (max (C.aOf μ X N) 0) ≤ Real.sqrt (C.Cmu * (1 + ((q / 2 : ℕ) : ℝ))) / Real.sqrt h := by
    rw [← Real.sqrt_div (by have := C.consts_pos2.1; positivity)]
    apply Real.sqrt_le_sqrt
    have hmu := C.muTilde_abs_le hμ hX hh1
    rw [aOf_eq]
    apply max_le
    · have : -(1 / h) * C.muTilde μ X N ≤ C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)) / h := by
        have h1 : -(1 / h) * C.muTilde μ X N = (-C.muTilde μ X N) / h := by ring
        rw [h1]
        exact div_le_div_of_nonneg_right (by linarith [abs_le.mp hmu]) hh0.le
      exact this
    · exact div_nonneg (mul_nonneg C.consts_pos2.1 (by positivity)) hh0.le
  have hexp : (C.Zof μ X N ((C.chain μ X N).jj 1 + 1) - C.Zof μ X N ((C.chain μ X N).jj 1)) *
      (|C.Zof μ X N ((C.chain μ X N).jj 1)| / 2 + Real.sqrt (max (C.aOf μ X N) 0)) ≤ C.tDw := by
    have hfac : |C.Zof μ X N ((C.chain μ X N).jj 1)| / 2 + Real.sqrt (max (C.aOf μ X N) 0) ≤
        ((C.cZ * C.δ0 + 2 * C.dp * C.η) / 2 + Real.sqrt (C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)))) / Real.sqrt h := by
      have := add_le_add (div_le_div_of_nonneg_right hZ1abs (by norm_num : (0 : ℝ) ≤ 2)) hamax
      calc _ ≤ _ := this
        _ = _ := by field_simp
    have hnn : 0 ≤ |C.Zof μ X N ((C.chain μ X N).jj 1)| / 2 + Real.sqrt (max (C.aOf μ X N) 0) := by positivity
    have hd0 : 0 ≤ C.Zof μ X N ((C.chain μ X N).jj 1 + 1) - C.Zof μ X N ((C.chain μ X N).jj 1) := sub_nonneg.mpr hZ12
    calc _ ≤ (C.dp * Real.sqrt h) * (((C.cZ * C.δ0 + 2 * C.dp * C.η) / 2 + Real.sqrt (C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)))) / Real.sqrt h) :=
          mul_le_mul hdiffZ hfac hnn (by positivity)
      _ = C.tDw := by unfold tDw; field_simp
  have hw : (C.chain μ X N).W ((C.chain μ X N).jj 1 + 1) ≤ C.tCw * (C.chain μ X N).W ((C.chain μ X N).jj 1) := by
    rw [hWj1, hWj2]
    have hr := Eminus_ratio (C.aOf μ X N) hZ12 hZ2
    refine le_trans hr ?_
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (Eminus_pos _ _).le
  exact hw

/-- **(S3) at the forbidden overlap `j_1`** (`app_thmA` Step 3, `engine.tex` case (ii)), derived from the chart fields. -/
lemma soft_transfer_one :
    ((C.chain μ X N).rescale1 lam).TransferAtΛ C.softLamC (F.step N) 1 := by
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hμ hX hN hh hV
  obtain ⟨-, hη, hdm, hdmp, -, hcF, -, hcZ⟩ := C.consts_pos
  have hP3' : ((C.chain μ X N).rescale1 lam).P = 3 := hP3
  set h := F.step N with hhdef
  have hh0 : 0 < h := step_pos (F := F) N
  have hh1 : h ≤ 1 := hh.trans C.softH1_le_one
  have hhη : h ≤ C.η / 2 := hh.trans C.softH1_le_eta
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh0
  have hs2 : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh0.le
  have hα := C.abs_alpha_le hX
  -- the bond
  have hAne : (C.chain μ X N).A ((C.chain μ X N).jj 1) ≠ 0 :=
    hV.A_ne_zero (p := 2) (mem_Icc.mpr ⟨by norm_num, by rw [hP3']; norm_num⟩) (j := (C.chain μ X N).jj 1)
      (mem_Icc.mpr ⟨le_rfl, hj12.le⟩)
  have hAeq : (C.chain μ X N).A ((C.chain μ X N).jj 1) = F.bondA μ N ((C.chain μ X N).jj 1) :=
    C.A_bond μ hμ X hX N hN ((C.chain μ X N).jj 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hApos : 0 < (C.chain μ X N).A ((C.chain μ X N).jj 1) := lt_of_le_of_ne (hAeq ▸ bondA_nonneg' F μ N _) (Ne.symm hAne)
  have hAle : (C.chain μ X N).A ((C.chain μ X N).jj 1) ≤ C.CA := hAeq ▸ C.bondA_le μ hμ N hN _
  -- weights
  have hWj1 : (C.chain μ X N).W ((C.chain μ X N).jj 1) = Eminus (C.aOf μ X N) (C.Zof μ X N ((C.chain μ X N).jj 1)) := by
    rw [C.W1_def μ hμ X hX N hN ((C.chain μ X N).jj 1) (mem_Icc.mpr ⟨hj0, le_rfl⟩)]
    unfold softLamVal
    exact div_div_self_eq _ _ (Ewell_pos _ _).ne'
  have hWj2 : (C.chain μ X N).W ((C.chain μ X N).jj 1 + 1) = Eminus (C.aOf μ X N) (C.Zof μ X N ((C.chain μ X N).jj 1 + 1)) :=
    C.W2_def μ hμ X hX N hN ((C.chain μ X N).jj 1 + 1) (mem_Icc.mpr ⟨le_rfl, by omega⟩)
  -- the coordinate at the two rows
  have hx12 : uNode h ((C.chain μ X N).jj 1 + 1) - C.uc μ - (uNode h ((C.chain μ X N).jj 1) - C.uc μ) = h := by
    unfold uNode; push_cast; ring
  have hx1lo : -(2 * C.η) ≤ uNode h ((C.chain μ X N).jj 1) - C.uc μ := by linarith
  have hx2hi : uNode h ((C.chain μ X N).jj 1 + 1) - C.uc μ ≤ 2 * C.η := by
    have : uNode h ((C.chain μ X N).jj 1 + 1) ≤ uNode h ((C.chain μ X N).jj 2 + 1) := uNode_mono_le hh0.le (by omega)
    linarith
  have hmvt1 := C.zeta_mvt hμ hα hx1lo (by linarith) hx2hi
  rw [hx12] at hmvt1
  have hx2le : uNode h ((C.chain μ X N).jj 1 + 1) - C.uc μ ≤ uNode h ((C.chain μ X N).jj 2) - C.uc μ := by
    have : uNode h ((C.chain μ X N).jj 1 + 1) ≤ uNode h ((C.chain μ X N).jj 2) := uNode_mono_le hh0.le (by omega)
    linarith
  have hx2d : uNode h ((C.chain μ X N).jj 2) - C.uc μ ≤ 2 * C.η := by
    have : uNode h ((C.chain μ X N).jj 2) ≤ uNode h ((C.chain μ X N).jj 2 + 1) := uNode_mono_le hh0.le (by omega)
    linarith
  have hmvt2 := C.zeta_mvt hμ hα (by linarith) hx2le hx2d
  have hz2neg : C.zeta μ (F.bandHi μ - X) (uNode h ((C.chain μ X N).jj 1 + 1) - C.uc μ) ≤ 0 := by
    have := mul_nonneg hdm.le (sub_nonneg.mpr hx2le)
    linarith [hmvt2.1, hza]
  have hz12 : C.zeta μ (F.bandHi μ - X) (uNode h ((C.chain μ X N).jj 1) - C.uc μ) ≤ C.zeta μ (F.bandHi μ - X) (uNode h ((C.chain μ X N).jj 1 + 1) - C.uc μ) := by
    have := mul_nonneg hdm.le hh0.le
    linarith [hmvt1.1]
  -- Z comparisons
  have hZ12 : C.Zof μ X N ((C.chain μ X N).jj 1) ≤ C.Zof μ X N ((C.chain μ X N).jj 1 + 1) := by
    rw [Zof_eq, Zof_eq]; exact div_le_div_of_nonneg_right hz12 hs.le
  have hZ2 : C.Zof μ X N ((C.chain μ X N).jj 1 + 1) ≤ 0 := by
    rw [Zof_eq]; exact div_nonpos_of_nonpos_of_nonneg hz2neg hs.le
  -- bound for zeta at x1
  have hz0 : |C.zeta μ (F.bandHi μ - X) 0| ≤ C.cZ * C.δ0 := by
    have := C.zeta_alpha μ hμ _ hα
    have h2 : C.cZ * |F.bandHi μ - X| ≤ C.cZ * C.δ0 := mul_le_mul_of_nonneg_left hα hcZ.le
    linarith
  have hmvt0 := C.zeta_mvt hμ hα hx1lo (by linarith : uNode h ((C.chain μ X N).jj 1) - C.uc μ ≤ 0) (by linarith : (0 : ℝ) ≤ 2 * C.η)
  have hzb1 : |C.zeta μ (F.bandHi μ - X) (uNode h ((C.chain μ X N).jj 1) - C.uc μ)| ≤ C.cZ * C.δ0 + 2 * C.dp * C.η := by
    have h1 := abs_le.mp hz0
    have h2 : C.dp * (0 - (uNode h ((C.chain μ X N).jj 1) - C.uc μ)) ≤ C.dp * (2 * C.η) :=
      mul_le_mul_of_nonneg_left (by linarith) hdp.le
    have hn := mul_nonneg hdm.le (by linarith : (0 : ℝ) ≤ 0 - (uNode h ((C.chain μ X N).jj 1) - C.uc μ))
    rw [abs_le]
    constructor <;> linarith [hmvt0.1, hmvt0.2]
  -- exponent of the one-step comparison
  have hdiffZ : C.Zof μ X N ((C.chain μ X N).jj 1 + 1) - C.Zof μ X N ((C.chain μ X N).jj 1) ≤ C.dp * Real.sqrt h := by
    rw [Zof_eq, Zof_eq, ← sub_div, div_le_iff₀ hs]
    have : C.dp * Real.sqrt h * Real.sqrt h = C.dp * h := by rw [mul_assoc, ← sq, hs2]
    rw [this]; exact hmvt1.2
  have hdiffZ0 : 0 ≤ C.zeta μ (F.bandHi μ - X) (uNode h ((C.chain μ X N).jj 1 + 1) - C.uc μ) / Real.sqrt h
      - C.zeta μ (F.bandHi μ - X) (uNode h ((C.chain μ X N).jj 1) - C.uc μ) / Real.sqrt h := by
    rw [← sub_div]; exact div_nonneg (sub_nonneg.mpr hz12) hs.le
  have hZ1abs : |C.Zof μ X N ((C.chain μ X N).jj 1)| ≤ (C.cZ * C.δ0 + 2 * C.dp * C.η) / Real.sqrt h := by
    rw [Zof_eq, abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right hzb1 hs.le
  have hamax : Real.sqrt (max (C.aOf μ X N) 0) ≤ Real.sqrt (C.Cmu * (1 + ((q / 2 : ℕ) : ℝ))) / Real.sqrt h := by
    rw [← Real.sqrt_div (by have := C.consts_pos2.1; positivity)]
    apply Real.sqrt_le_sqrt
    have hmu := C.muTilde_abs_le hμ hX hh1
    rw [aOf_eq]
    apply max_le
    · have : -(1 / h) * C.muTilde μ X N ≤ C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)) / h := by
        have h1 : -(1 / h) * C.muTilde μ X N = (-C.muTilde μ X N) / h := by ring
        rw [h1]
        exact div_le_div_of_nonneg_right (by linarith [abs_le.mp hmu]) hh0.le
      exact this
    · exact div_nonneg (mul_nonneg C.consts_pos2.1 (by positivity)) hh0.le
  have hexp : (C.Zof μ X N ((C.chain μ X N).jj 1 + 1) - C.Zof μ X N ((C.chain μ X N).jj 1)) *
      (|C.Zof μ X N ((C.chain μ X N).jj 1)| / 2 + Real.sqrt (max (C.aOf μ X N) 0)) ≤ C.tDw := by
    have hfac : |C.Zof μ X N ((C.chain μ X N).jj 1)| / 2 + Real.sqrt (max (C.aOf μ X N) 0) ≤
        ((C.cZ * C.δ0 + 2 * C.dp * C.η) / 2 + Real.sqrt (C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)))) / Real.sqrt h := by
      have := add_le_add (div_le_div_of_nonneg_right hZ1abs (by norm_num : (0 : ℝ) ≤ 2)) hamax
      calc _ ≤ _ := this
        _ = _ := by field_simp
    have hnn : 0 ≤ |C.Zof μ X N ((C.chain μ X N).jj 1)| / 2 + Real.sqrt (max (C.aOf μ X N) 0) := by positivity
    have hd0 : 0 ≤ C.Zof μ X N ((C.chain μ X N).jj 1 + 1) - C.Zof μ X N ((C.chain μ X N).jj 1) := sub_nonneg.mpr hZ12
    calc _ ≤ (C.dp * Real.sqrt h) * (((C.cZ * C.δ0 + 2 * C.dp * C.η) / 2 + Real.sqrt (C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)))) / Real.sqrt h) :=
          mul_le_mul hdiffZ hfac hnn (by positivity)
      _ = C.tDw := by unfold tDw; field_simp
  have hw := C.soft_Wratio hμ hX hN hh hV
  -- the margins `k_2 >= c/h`
  have hωeq : |(C.chain μ X N).ω 1 h| = Real.sqrt h := by
    obtain ⟨-, -, -, -, -, hω, -⟩ := C.patch1_eq μ hμ X hX N hN
    have : (C.chain μ X N).ω 1 h = Real.sqrt h := by rw [hω]; exact C.omega_sqrtW μ hμ X hX N hN
    rw [this, abs_of_pos hs]
  have hM1 : (C.chain μ X N).M ((C.chain μ X N).jj 1) = Mbal (-((((C.chain μ X N).jj 1 : ℤ) : ℝ) + 1 / 2)) (C.Y μ X (uNode h ((C.chain μ X N).jj 1)) / Real.sqrt h) :=
    C.M1_def μ hμ X hX N hN ((C.chain μ X N).jj 1) (mem_Icc.mpr ⟨hj0, le_rfl⟩)
  have hM2 : (C.chain μ X N).M ((C.chain μ X N).jj 1 + 1) = Mbal (C.aOf μ X N) (C.Zof μ X N ((C.chain μ X N).jj 1 + 1)) :=
    C.M2_def μ hμ X hX N hN ((C.chain μ X N).jj 1 + 1) (mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hmar1 : (C.cF / 4) / h ≤ |(C.Y μ X (uNode h ((C.chain μ X N).jj 1)) / Real.sqrt h) ^ 2 / 4 + -((((C.chain μ X N).jj 1 : ℤ) : ℝ) + 1 / 2)| := by
    have hu0 : 0 ≤ uNode h ((C.chain μ X N).jj 1) := by
      unfold uNode
      have : (0 : ℝ) ≤ (((C.chain μ X N).jj 1 : ℤ) : ℝ) := by exact_mod_cast hj0
      positivity
    have hYf := (C.Y_forb μ hμ X hX (uNode h ((C.chain μ X N).jj 1)) (Set.mem_Icc.mpr ⟨hu0, by linarith⟩)).1
    have e : (C.Y μ X (uNode h ((C.chain μ X N).jj 1)) / Real.sqrt h) ^ 2 / 4 + -((((C.chain μ X N).jj 1 : ℤ) : ℝ) + 1 / 2)
        = (C.Y μ X (uNode h ((C.chain μ X N).jj 1)) ^ 2 / 4 - uNode h ((C.chain μ X N).jj 1)) / h := by
      rw [div_pow, hs2]; unfold uNode; field_simp; ring
    rw [e, abs_of_nonneg (div_nonneg (by linarith) hh0.le)]
    exact div_le_div_of_nonneg_right (by linarith) hh0.le
  have hmar2 : (C.cz1 / 8) / h ≤ |C.Zof μ X N ((C.chain μ X N).jj 1 + 1) ^ 2 / 4 + C.aOf μ X N| := by
    rw [Z2_add_a]
    have hq := C.Zq_lb hμ hX hh (x := uNode h ((C.chain μ X N).jj 1 + 1) - C.uc μ) (by
        rw [abs_of_neg (by linarith)]; linarith) (by rw [abs_of_neg (by linarith)]; linarith)
    rw [abs_of_nonneg (div_nonneg (by linarith [C.consts_pos2.2]) hh0.le)]
    exact div_le_div_of_nonneg_right hq hh0.le
  have hMM : (C.chain μ X N).M ((C.chain μ X N).jj 1) * (C.chain μ X N).M ((C.chain μ X N).jj 1 + 1) ≤ C.tCM * Real.sqrt h := by
    rw [hM1, hM2]
    exact Mbal_prod_le _ _ _ _ (C.cF / 4) (C.cz1 / 8) h (by linarith [C.consts_pos.2.2.2.2.2.1]) (by linarith [C.consts_pos2.2]) hh0 hmar1 hmar2
  have hMMnn : 0 ≤ (C.chain μ X N).M ((C.chain μ X N).jj 1) * (C.chain μ X N).M ((C.chain μ X N).jj 1 + 1) := by
    rw [hM1, hM2]; exact mul_nonneg (Mbal_pos _ _).le (Mbal_pos _ _).le
  have hAM : (C.chain μ X N).A ((C.chain μ X N).jj 1) * ((C.chain μ X N).M ((C.chain μ X N).jj 1) * (C.chain μ X N).M ((C.chain μ X N).jj 1 + 1)) ≤ C.tCω * |(C.chain μ X N).ω 1 h| := by
    rw [hωeq]
    unfold tCω
    calc (C.chain μ X N).A ((C.chain μ X N).jj 1) * ((C.chain μ X N).M ((C.chain μ X N).jj 1) * (C.chain μ X N).M ((C.chain μ X N).jj 1 + 1)) ≤ C.CA * (C.tCM * Real.sqrt h) :=
          mul_le_mul hAle hMM hMMnn C.consts_pos3.1
      _ = C.CA * C.tCM * Real.sqrt h := by ring
  have key := hV.transferAt_forbidden (p := 1) le_rfl (by rw [hP3']; norm_num) C.tCw C.tCω hApos hw hAM
  exact LadderData.TransferAtΛ.mono (lt_of_lt_of_le one_pos C.tΛ1_ge) C.tΛ1_le key


end Trans

/-- `phi` is `v . w` (unfolding of `ladderSeq` at the site `u_k`). -/
lemma phi_eq_dot (D : LadderData) (h : ℝ) (α : Fin 2) (p : ℕ) (k : ℤ) :
    D.phi h α p k = dot (vrow (D.AA p) (D.BB p) (uNode h k) h) (D.wf p α (uNode h k) h) := rfl

section Swap

/-- **The swapped pair is a constant combination of the `-` pair at every row of patch 3** (`wf2_eq`, `wf3_eq`, `shared_PC`, `pcSwap_eq_pcMinus`): for `a <= 0`,
`phi^{(1)}_3 = sqrt(pi/2) cos(pi a) phi^{(1)}_2 - sin(pi a) phi^{(2)}_2`, `phi^{(2)}_3 = sin(pi a) phi^{(1)}_2 + sqrt(2/pi) cos(pi a) phi^{(2)}_2`; for `a > 0` the two patches carry the same pair. -/
lemma phi_swap_rel {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) {μ : Par} (hμ : μ ∈ P) {X : ℝ}
    (hX : |X - F.bandHi μ| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N) {k : ℤ}
    (hk1 : (C.chain μ X N).jj 1 ≤ (C.chain μ X N).jj 2) (hk2 : (C.chain μ X N).jj 2 ≤ k) (hk3 : k ≤ (C.chain μ X N).NR + 1) :
    (C.aOf μ X N ≤ 0 →
      (C.chain μ X N).phi (F.step N) 0 3 k = Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * C.aOf μ X N) * (C.chain μ X N).phi (F.step N) 0 2 k
        + (-Real.sin (Real.pi * C.aOf μ X N)) * (C.chain μ X N).phi (F.step N) 1 2 k ∧
      (C.chain μ X N).phi (F.step N) 1 3 k = Real.sin (Real.pi * C.aOf μ X N) * (C.chain μ X N).phi (F.step N) 0 2 k
        + Real.sqrt (2 / Real.pi) * Real.cos (Real.pi * C.aOf μ X N) * (C.chain μ X N).phi (F.step N) 1 2 k) ∧
    (0 < C.aOf μ X N →
      (C.chain μ X N).phi (F.step N) 0 3 k = (C.chain μ X N).phi (F.step N) 0 2 k ∧
      (C.chain μ X N).phi (F.step N) 1 3 k = (C.chain μ X N).phi (F.step N) 1 2 k) := by
  obtain ⟨hdd2, hω2, hdd3, hpp3, hqq3, hPiP3, hPiM3, hω3, hAA3, hBB3⟩ := C.shared_PC μ hμ X hX N hN
  have hw2 := C.wf2_eq μ hμ X hX N hN k (mem_Icc.mpr ⟨le_trans hk1 hk2, hk3⟩)
  have hw3 := C.wf3_eq μ hμ X hX N hN k (mem_Icc.mpr ⟨hk2, hk3⟩)
  set a := C.aOf μ X N with ha
  set z := C.Zof μ X N k with hz
  set h := F.step N with hhdef
  have hU : ∀ b, Differentiable ℝ (U b) := fun b => by
    have := hf.smooth_U.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ ⊤ (fun w : ℝ => (b, w)))
    exact this.differentiable (by simp)
  have hV' : ∀ b, Differentiable ℝ (V b) := fun b => by
    have := hf.smooth_V.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ ⊤ (fun w : ℝ => (b, w)))
    exact this.differentiable (by simp)
  have hw3' : ∀ α : Fin 2, (C.chain μ X N).wf 3 α (uNode h k) h = ![pcSwap U V a α z, √h * deriv (pcSwap U V a α) z] := hw3
  have hw2' : ∀ α : Fin 2, (C.chain μ X N).wf 2 α (uNode h k) h = ![pcMinus U V a α z, √h * deriv (pcMinus U V a α) z] := hw2
  have hphi : ∀ (α : Fin 2) (p : ℕ), (C.chain μ X N).phi h α p k =
      dot (vrow ((C.chain μ X N).AA p) ((C.chain μ X N).BB p) (uNode h k) h) ((C.chain μ X N).wf p α (uNode h k) h) :=
    fun α p => phi_eq_dot _ h α p k
  refine ⟨fun hale => ?_, fun hapos => ?_⟩
  · -- a <= 0
    have hrel := pcSwap_eq_pcMinus hf hale
    have hd0 : DifferentiableAt ℝ (pcMinus U V a 0) z := by
      have : pcMinus U V a 0 = fun w => kappaBal a * U a (-w) := by
        funext w; simp [pcMinus, hale, ut]
      rw [this]
      exact (((hU a).comp differentiable_neg).const_mul _) z
    have hd1 : DifferentiableAt ℝ (pcMinus U V a 1) z := by
      have : pcMinus U V a 1 = fun w => -(Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * V a (-w)) := by
        funext w; simp [pcMinus, hale, vt]
      rw [this]
      exact ((((hV' a).comp differentiable_neg).const_mul _).neg) z
    have hs0 : pcSwap U V a 0 = fun w => (Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * a)) * pcMinus U V a 0 w
        + (-Real.sin (Real.pi * a)) * pcMinus U V a 1 w := by
      funext w; rw [(hrel w).1]; ring
    have hs1 : pcSwap U V a 1 = fun w => (Real.sin (Real.pi * a)) * pcMinus U V a 0 w
        + (Real.sqrt (2 / Real.pi) * Real.cos (Real.pi * a)) * pcMinus U V a 1 w := by
      funext w; rw [(hrel w).2]
    have hD0 : deriv (pcSwap U V a 0) z = (Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * a)) * deriv (pcMinus U V a 0) z
        + (-Real.sin (Real.pi * a)) * deriv (pcMinus U V a 1) z := by
      rw [hs0]
      exact ((hd0.hasDerivAt.const_mul _).add (hd1.hasDerivAt.const_mul _)).deriv
    have hD1 : deriv (pcSwap U V a 1) z = (Real.sin (Real.pi * a)) * deriv (pcMinus U V a 0) z
        + (Real.sqrt (2 / Real.pi) * Real.cos (Real.pi * a)) * deriv (pcMinus U V a 1) z := by
      rw [hs1]
      exact ((hd0.hasDerivAt.const_mul _).add (hd1.hasDerivAt.const_mul _)).deriv
    have hs0z := congrFun hs0 z
    have hs1z := congrFun hs1 z
    constructor
    · rw [hphi, hphi, hphi, hAA3, hBB3, hw3' 0, hw2' 0, hw2' 1]
      simp only [dot, vrow, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hs0z, hD0]; ring
    · rw [hphi, hphi, hphi, hAA3, hBB3, hw3' 1, hw2' 0, hw2' 1]
      simp only [dot, vrow, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hs1z, hD1]; ring
  · -- a > 0
    have hapos' : ¬ a ≤ 0 := not_le.mpr hapos
    have e : ∀ α : Fin 2, pcSwap U V a α = pcMinus U V a α := by
      intro α
      fin_cases α <;> simp [pcSwap, pcMinus, hapos']
    constructor
    · rw [hphi, hphi, hAA3, hBB3, hw3' 0, hw2' 0, e]
    · rw [hphi, hphi, hAA3, hBB3, hw3' 1, hw2' 1, e]

end Swap



section Two

variable {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC)
  {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : |X - F.bandHi μ| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N)
  (hh : F.step N ≤ C.softH1) {lam : ℝ}
  (hV : ((C.chain μ X N).rescale1 lam).PreValid C.cs (F.step N) m)

include hf hμ hX hN hh hV

/-- **(S3) at the switch bond `j_2`** (`app_thmA` Step 2, case (i) of (S3)): the transfer matrix is `(M_-(a) S)^{-1}`, bounded by `2 <= Lambda`; `exp(-Z^2/4) <= E_- <= 1` at `j_2`. -/
lemma soft_transfer_two :
    ((C.chain μ X N).rescale1 lam).TransferAtΛ C.softLamC (F.step N) 2 := by
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hμ hX hN hh hV
  obtain ⟨-, hη, hdm, hdmp, -, hcF, -, hcZ⟩ := C.consts_pos
  have hP3' : ((C.chain μ X N).rescale1 lam).P = 3 := hP3
  have hh0 : 0 < F.step N := step_pos (F := F) N
  have hh1 : F.step N ≤ 1 := hh.trans C.softH1_le_one
  have hhη : F.step N ≤ C.η / 2 := hh.trans C.softH1_le_eta
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hs : 0 < Real.sqrt (F.step N) := Real.sqrt_pos.mpr hh0
  have hs2 : Real.sqrt (F.step N) ^ 2 = F.step N := Real.sq_sqrt hh0.le
  have hα := C.abs_alpha_le hX
  have hΛ2 := C.softLamC_ge_two
  have hphi2 : ∀ (α : Fin 2) (k : ℤ), ((C.chain μ X N).rescale1 lam).phi (F.step N) α 2 k = (C.chain μ X N).phi (F.step N) α 2 k :=
    fun α k => LadderData.phi_rescale1_of_ne _ lam _ α (by norm_num) k
  have hphi3 : ∀ (α : Fin 2) (k : ℤ), ((C.chain μ X N).rescale1 lam).phi (F.step N) α 3 k = (C.chain μ X N).phi (F.step N) α 3 k :=
    fun α k => LadderData.phi_rescale1_of_ne _ lam _ α (by norm_num) k
  have hne := hV.det_ne_zero (p := 2) (mem_Icc.mpr ⟨by norm_num, by rw [hP3']; norm_num⟩) (j := (C.chain μ X N).jj 2)
    (mem_Icc.mpr ⟨hj12.le, le_rfl⟩)
  rw [hphi2, hphi2, hphi2, hphi2] at hne
  have hr0 := C.phi_swap_rel hf hμ hX hN (k := (C.chain μ X N).jj 2) hj12.le le_rfl (by omega)
  have hr1 := C.phi_swap_rel hf hμ hX hN (k := (C.chain μ X N).jj 2 + 1) hj12.le (by omega) (by omega)
  by_cases hale : C.aOf μ X N ≤ 0
  · obtain ⟨hr0a, hr0b⟩ := hr0.1 hale
    obtain ⟨hr1a, hr1b⟩ := hr1.1 hale
    -- the weight at j_2
    have hWj2 : (C.chain μ X N).W ((C.chain μ X N).jj 2) = Ewell (C.aOf μ X N) |C.Zof μ X N ((C.chain μ X N).jj 2)| := by
      rw [C.W2_def μ hμ X hX N hN ((C.chain μ X N).jj 2) (mem_Icc.mpr ⟨by omega, le_rfl⟩)]
      exact Eminus_of_nonpos hale _
    -- |zeta_{j_2}| <= d_+ h
    have hx12 : uNode (F.step N) ((C.chain μ X N).jj 2 + 1) - C.uc μ - (uNode (F.step N) ((C.chain μ X N).jj 2) - C.uc μ) = F.step N := by
      unfold uNode; push_cast; ring
    have hx2lo : -(2 * C.η) ≤ uNode (F.step N) ((C.chain μ X N).jj 2) - C.uc μ := by
      have : uNode (F.step N) ((C.chain μ X N).jj 1 + 1) ≤ uNode (F.step N) ((C.chain μ X N).jj 2) := uNode_mono_le hh0.le (by omega)
      linarith
    have hmvt := C.zeta_mvt hμ hα hx2lo (by linarith) hx3
    rw [hx12] at hmvt
    have hzlo : -(C.dp * F.step N) ≤ C.zeta μ (F.bandHi μ - X) (uNode (F.step N) ((C.chain μ X N).jj 2) - C.uc μ) := by
      linarith [hmvt.2]
    have hZ2 : C.Zof μ X N ((C.chain μ X N).jj 2) ^ 2 ≤ 1 := by
      rw [Zof_eq, div_pow, hs2, div_le_one hh0]
      have hdh : C.dp ^ 2 * F.step N ≤ 1 := by
        have := C.softH1_le_dp
        have h2 := hh.trans this
        rw [le_div_iff₀ (by positivity)] at h2
        linarith
      have hsq : C.zeta μ (F.bandHi μ - X) (uNode (F.step N) ((C.chain μ X N).jj 2) - C.uc μ) ^ 2 ≤ (C.dp * F.step N) ^ 2 := by
        apply sq_le_sq'
        · linarith
        · linarith
      calc _ ≤ (C.dp * F.step N) ^ 2 := hsq
        _ = (C.dp ^ 2 * F.step N) * F.step N := by ring
        _ ≤ 1 * F.step N := mul_le_mul_of_nonneg_right hdh hh0.le
        _ = F.step N := one_mul _
    have hWle : (C.chain μ X N).W ((C.chain μ X N).jj 2) ≤ 1 := by
      rw [hWj2]; exact Ewell_le_one _ (abs_nonneg _)
    have hWpos : 0 < (C.chain μ X N).W ((C.chain μ X N).jj 2) := by rw [hWj2]; exact Ewell_pos _ _
    have hWge : (3 : ℝ) / 4 ≤ (C.chain μ X N).W ((C.chain μ X N).jj 2) := by
      rw [hWj2]
      have h1 := Ewell_ge_exp (C.aOf μ X N) (abs_nonneg (C.Zof μ X N ((C.chain μ X N).jj 2)))
      rw [sq_abs] at h1
      have h2 : Real.exp (-(1 / 4 : ℝ)) ≤ Real.exp (-(C.Zof μ X N ((C.chain μ X N).jj 2) ^ 2 / 4)) :=
        Real.exp_le_exp.mpr (by linarith)
      have h3 := Real.add_one_le_exp (-(1 / 4 : ℝ))
      linarith
    -- the numbers
    have hsq1 : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
      rw [← Real.sqrt_mul (by positivity)]
      have : Real.pi / 2 * (2 / Real.pi) = 1 := by field_simp
      rw [this, Real.sqrt_one]
    have hs1 := Real.sin_sq_add_cos_sq (Real.pi * C.aOf μ X N)
    have hdet : Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * C.aOf μ X N) * (Real.sqrt (2 / Real.pi) * Real.cos (Real.pi * C.aOf μ X N))
        - Real.sin (Real.pi * C.aOf μ X N) * (-Real.sin (Real.pi * C.aOf μ X N)) = 1 := by
      linear_combination (Real.cos (Real.pi * C.aOf μ X N) ^ 2) * hsq1 + hs1
    have hsqa : Real.sqrt (Real.pi / 2) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      linarith [Real.pi_le_four]
    have hsqd : Real.sqrt (2 / Real.pi) ≤ 1 := by
      rw [Real.sqrt_le_one]
      rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
    have hcos := Real.abs_cos_le_one (Real.pi * C.aOf μ X N)
    have hsin := Real.abs_sin_le_one (Real.pi * C.aOf μ X N)
    have ha : |Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * C.aOf μ X N)| ≤ C.softLamC := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc _ ≤ Real.sqrt (Real.pi / 2) * 1 := mul_le_mul_of_nonneg_left hcos (Real.sqrt_nonneg _)
        _ ≤ 2 := by linarith
        _ ≤ _ := hΛ2
    have hd : |Real.sqrt (2 / Real.pi) * Real.cos (Real.pi * C.aOf μ X N)| ≤ C.softLamC := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc _ ≤ Real.sqrt (2 / Real.pi) * 1 := mul_le_mul_of_nonneg_left hcos (Real.sqrt_nonneg _)
        _ ≤ 2 := by linarith
        _ ≤ _ := hΛ2
    have hW2 : (C.chain μ X N).W ((C.chain μ X N).jj 2) ^ 2 ≤ 1 := pow_le_one₀ hWpos.le hWle
    have hW2lo : (9 : ℝ) / 16 ≤ (C.chain μ X N).W ((C.chain μ X N).jj 2) ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) hWge 2
      linarith [this]
    have hb : |Real.sin (Real.pi * C.aOf μ X N)| ≤ C.softLamC * ((C.chain μ X N).W ((C.chain μ X N).jj 2) ^ 2)⁻¹ := by
      have hinv : 1 ≤ ((C.chain μ X N).W ((C.chain μ X N).jj 2) ^ 2)⁻¹ := (one_le_inv₀ (by positivity)).mpr hW2
      calc |Real.sin (Real.pi * C.aOf μ X N)| ≤ 1 := hsin
        _ ≤ C.softLamC * 1 := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by linarith)
    have hc : |-Real.sin (Real.pi * C.aOf μ X N)| ≤ C.softLamC * (C.chain μ X N).W ((C.chain μ X N).jj 2) ^ 2 := by
      rw [abs_neg]
      calc |Real.sin (Real.pi * C.aOf μ X N)| ≤ 1 := hsin
        _ ≤ 2 * (9 / 16) := by norm_num
        _ ≤ _ := mul_le_mul hΛ2 hW2lo (by norm_num) (by linarith)
    exact LadderData.TransferAtΛ_of_linear (D := (C.chain μ X N).rescale1 lam) (h := F.step N) (p := 2) C.softLamC_ge
      _ _ _ _ hdet (by rw [hphi3, hphi2, hphi2]; exact hr0a) (by rw [hphi3, hphi2, hphi2]; exact hr1a)
      (by rw [hphi3, hphi2, hphi2]; exact hr0b) (by rw [hphi3, hphi2, hphi2]; exact hr1b) (by rw [hphi2, hphi2, hphi2, hphi2]; exact hne)
      ha hb hc hd
  · have hapos : 0 < C.aOf μ X N := not_le.mp hale
    obtain ⟨hr0a, hr0b⟩ := hr0.2 hapos
    obtain ⟨hr1a, hr1b⟩ := hr1.2 hapos
    have hΛpos : 0 < C.softLamC := by linarith
    exact LadderData.TransferAtΛ_of_linear (D := (C.chain μ X N).rescale1 lam) (h := F.step N) (p := 2) C.softLamC_ge
      1 0 0 1 (by norm_num)
      (by rw [hphi3, hphi2, hphi2, one_mul, zero_mul, add_zero]; exact hr0a)
      (by rw [hphi3, hphi2, hphi2, one_mul, zero_mul, add_zero]; exact hr1a)
      (by rw [hphi3, hphi2, hphi2, one_mul, zero_mul, zero_add]; exact hr0b)
      (by rw [hphi3, hphi2, hphi2, one_mul, zero_mul, zero_add]; exact hr1b)
      (by rw [hphi2, hphi2, hphi2, hphi2]; exact hne)
      (by rw [abs_one]; linarith) (by rw [abs_zero]; positivity) (by rw [abs_zero]; positivity) (by rw [abs_one]; linarith)

end Two

section ValidDerived

variable {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC)
  {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : |X - F.bandHi μ| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N)
  (hh : F.step N ≤ C.softH1) {lam : ℝ}
  (hV : ((C.chain μ X N).rescale1 lam).PreValid C.cs (F.step N) m)

include hf hμ hX hN hh hV

/-- **The full engine hypotheses of the rescaled soft chain are derived**: `PreValid` (the chart field `valid`) plus (S3) at `j_1` (forbidden overlap) and `j_2` (bounded overlap `M_-(a) S`),
for the constants `csT = {cs with Lambda := softLamC}`.  (Finding F-W2-7 resolved: (S3) is no longer a field.) -/
theorem soft_valid : ((C.chain μ X N).rescale1 lam).Valid C.csT (F.step N) m := by
  obtain ⟨hP3, -⟩ := C.soft_pos hμ hX hN hh hV
  have hP3' : ((C.chain μ X N).rescale1 lam).P = 3 := hP3
  exact hV.toValid C.softLamC C.softLamC_ge (fun p hp1 hp2 => by
    have hp : p = 1 ∨ p = 2 := by rw [hP3'] at hp2; omega
    rcases hp with rfl | rfl
    · exact C.soft_transfer_one hμ hX hN hh hV
    · exact C.soft_transfer_two hf hμ hX hN hh hV)

end ValidDerived


end SoftEdgeChart

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.SoftEdgeChart.soft_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.SoftEdgeChart.soft_valid

end FormalResearch.JacobiEigenvectors.Charts
