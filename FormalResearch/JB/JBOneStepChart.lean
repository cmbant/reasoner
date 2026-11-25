module

public import Mathlib
public import FormalResearch.JB.JBOneStepAux
public import FormalResearch.JB.JBRatio

/-!
# Paper J, Theorem B reduction: one chart (Steps 2-4 of `thm:thb-onestep`)

Source: Paper J, `/home/user/scratch/paperJ2/thmB.tex`, proof of `thm:thb-onestep`, Steps 2 (scalar
ratios `σ^{[m]} = (1 + ρ) σ^{[m+1]}`, via `jb_ratio`), 3 (carriers via `jb_glue` / `jb_glue_rev`) and 4
(`‖H^{[m]}_c - H^{[m+1]}_c‖ ≤ C₁ h^m`), for one chart `c : Chart D R cols` with `c.Ok cs m h U`, given
`‖host1‖ ≤ 2` (Step 1).  All constants depend on `cs` only.

* `chart_ratio` (Step 2), `chart_carriers` (Step 3), `chart_diff` (Step 4, constant `chartConst cs`).
-/

@[expose] public section

namespace FormalResearch.JB

open Matrix FormalResearch.MatrixAnalysis
open scoped Matrix.Norms.L2Operator

section Helpers

variable {R : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem Ysh_scale (s yext : κ → ℝ) (Y : Matrix (Fin R) κ ℝ) (n : Fin R) (k : κ) :
    Ysh (fun k => s k * yext k) (Matrix.of fun n k => s k * Y n k) n k = s k * Ysh yext Y n k := by
  unfold Ysh; split_ifs <;> simp

theorem YshRev_scale (s yext : κ → ℝ) (Y : Matrix (Fin R) κ ℝ) (n : Fin R) (k : κ) :
    YshRev (fun k => s k * yext k) (Matrix.of fun n k => s k * Y n k) n k = s k * YshRev yext Y n k := by
  unfold YshRev; split_ifs <;> simp

/-- A matrix supported on one row has operator norm at most the `ℓ²` norm of that row. -/
theorem norm_le_of_single_row (E : Matrix (Fin R) κ ℝ) (n0 : Fin R)
    (h0 : ∀ n, n ≠ n0 → ∀ k, E n k = 0) : ‖E‖ ≤ jbL2 Finset.univ (fun k => E n0 k) := by
  refine (l2_opNorm_le_sqrt_frobSq E).trans (le_of_eq ?_)
  unfold frobSq jbL2
  congr 1
  rw [Finset.sum_eq_single n0]
  · intro n _ hn; exact Finset.sum_eq_zero fun k _ => by rw [h0 n hn k]; simp
  · simp

theorem norm_extRow_le (ω : Fin R → ℝ) (yext : κ → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (h : ∀ n : Fin R, n.val + 1 = R → jbL2 Finset.univ (fun k => ω n * yext k) ≤ B) :
    ‖extRow ω yext‖ ≤ B := by
  by_cases hex : ∃ n : Fin R, n.val + 1 = R
  · obtain ⟨n0, hn0⟩ := hex
    refine (norm_le_of_single_row _ n0 ?_).trans ?_
    · intro n hn k
      simp only [extRow, of_apply]
      rw [ite_eq_right]
      intro h'; exact hn (Fin.ext (by omega))
    · have := h n0 hn0
      simpa [extRow, hn0] using this
  · have : extRow ω yext = 0 := by
      ext n k
      simp only [extRow, of_apply, Matrix.zero_apply]
      rw [ite_eq_right]; intro h'; exact hex ⟨n, h'⟩
    rw [this]; simpa using hB0

theorem norm_extRowRev_le (ω : Fin R → ℝ) (yext : κ → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (h : ∀ n : Fin R, n.val = 0 → jbL2 Finset.univ (fun k => ω n * yext k) ≤ B) :
    ‖extRowRev ω yext‖ ≤ B := by
  by_cases hex : ∃ n : Fin R, n.val = 0
  · obtain ⟨n0, hn0⟩ := hex
    refine (norm_le_of_single_row _ n0 ?_).trans ?_
    · intro n hn k
      simp only [extRowRev, of_apply]
      rw [ite_eq_right]
      intro h'; exact hn (Fin.ext (by omega))
    · have := h n0 hn0
      simpa [extRowRev, hn0] using this
  · have : extRowRev ω yext = 0 := by
      ext n k
      simp only [extRowRev, of_apply, Matrix.zero_apply]
      rw [ite_eq_right]; intro h'; exact hex ⟨n, h'⟩
    rw [this]; simpa using hB0

theorem glue_arith {K ωmax h Fn En CE Yn Ytn : ℝ} (hK0 : 0 ≤ K) (hω : 0 ≤ ωmax) (hh0 : 0 ≤ h)
    (hh1 : h ≤ 1) (hk : h * K * ωmax ≤ 1 / 2) (hF : Fn ≤ 2) (hE : En ≤ CE) (hE0 : 0 ≤ En)
    (hY : Yn ≤ K * (Fn + h * En) / (1 - h * K * ωmax))
    (hYt : Ytn ≤ K * ((ωmax + 1) * Yn + En)) :
    Yn ≤ 2 * K * (2 + CE) ∧ Ytn ≤ K * ((ωmax + 1) * (2 * K * (2 + CE)) + CE) := by
  have hd : 0 < 1 - h * K * ωmax := by linarith
  have hhE : h * En ≤ En := mul_le_of_le_one_left hE0 hh1
  have hCE : 0 ≤ CE := hE0.trans hE
  have hnum : K * (Fn + h * En) ≤ K * (2 + CE) :=
    mul_le_mul_of_nonneg_left (by linarith) hK0
  have hY2 : Yn ≤ 2 * K * (2 + CE) := by
    refine hY.trans ((div_le_iff₀ hd).2 ?_)
    have : 0 ≤ K * (2 + CE) := by positivity
    nlinarith
  refine ⟨hY2, hYt.trans ?_⟩
  gcongr

end Helpers

namespace Chart

variable {D R : ℕ} {cols : Finset (Fin D)}

theorem row_injective (c : Chart D R cols) : Function.Injective c.row := by
  intro a b hab
  have := congrArg Fin.val hab
  simp only [Chart.row] at this
  exact Fin.ext (by omega)

/-- The changed carrier: `y` for even `m`, `ỹ` for odd `m` (`κ_m` multiplies `g_m ∘ y` resp. `B_m ∘ ỹ`). -/
def wsel (c : Chart D R cols) (m : ℕ) : Matrix (Fin R) cols ℝ :=
  if m % 2 = 0 then c.y else c.yt

/-- The carrier `Y' = (σ^{[m+1]}_k y_{nk})`. -/
def Y' (c : Chart D R cols) : Matrix (Fin R) cols ℝ := Matrix.of fun n k => c.σ1 k * c.y n k

/-- The carrier `Ỹ' = (σ^{[m+1]}_k ỹ_{nk})`. -/
def Yt' (c : Chart D R cols) : Matrix (Fin R) cols ℝ := Matrix.of fun n k => c.σ1 k * c.yt n k

variable {cs : OneStepConsts} {m : ℕ} {h : ℝ} {U : Matrix (Fin D) (Fin D) ℝ} {c : Chart D R cols}

theorem phi_diff (hc : c.Ok cs m h U) (n : Fin R) (k : cols) :
    c.phi0 h n k - c.phi1 h n k = -(h ^ m * c.κ n k * c.wsel m n k) := by
  have hA := hc.parity_A n k
  have hB := hc.parity_B n k
  rw [phi0_apply, phi1_apply]
  unfold wsel
  rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
  · rw [h0] at hA hB
    simp only [h0, if_true]
    linear_combination (-(c.y n k)) * hA + (-(c.yt n k)) * hB
  · rw [h1] at hA hB
    simp only [h1, one_ne_zero, ite_false]
    linear_combination (-(c.y n k)) * hA + (-(c.yt n k)) * hB

theorem jbL2_wsel_le (S : Finset (Fin R)) (k : cols) :
    jbL2 S (fun n => c.wsel m n k) ≤ jbL2 S (fun n => c.y n k) + jbL2 S (fun n => c.yt n k) := by
  have h1 := jbL2_nonneg S (fun n => c.y n k)
  have h2 := jbL2_nonneg S (fun n => c.yt n k)
  unfold wsel
  split_ifs <;> linarith

/-- Step 2 (scalar ratios): `σ^{[m]}_k = (1 + ρ_k) σ^{[m+1]}_k` with `|ρ_k| ≤ 2 (K C₄ + 4 C / c₀) h^m`. -/
theorem chart_ratio (hc : c.Ok cs m h U) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (h2 : cs.K * cs.C4 * h ^ m ≤ 1 / 2) (h3 : cs.C * h ^ m ≤ cs.c0 / 2) (k : cols) :
    c.σ1 k ≠ 0 ∧ |c.σ0 k / c.σ1 k - 1| ≤ 2 * (cs.K * cs.C4 + 4 * cs.C / cs.c0) * h ^ m := by
  have hc0 := cs.c0_pos
  have hKn := cs.K_nonneg
  have hC4 := cs.C4_nonneg
  have hCn := cs.C_nonneg
  have hhm : 0 < h ^ m := pow_pos hh0 m
  set ε := cs.K * cs.C4 * h ^ m with hε
  set δ := cs.C * h ^ m with hδ
  have hε0 : 0 ≤ ε := by positivity
  have hδ0 : 0 ≤ δ := by positivity
  -- the difference of the profiles on `P_k`
  have hdiff : jbL2 (c.P k) (fun n => c.phi0 h n k - c.phi1 h n k) ≤
      ε * jbL2 (c.P k) (fun n => c.phi1 h n k) := by
    have e1 : jbL2 (c.P k) (fun n => c.phi0 h n k - c.phi1 h n k) ≤
        (h ^ m * cs.K) * jbL2 (c.P k) (fun n => c.wsel m n k) := by
      refine jbL2_le_mul _ _ _ (by positivity) fun n _ => ?_
      rw [phi_diff hc, abs_neg, abs_mul, abs_mul, abs_of_pos hhm]
      have := (hc.schur_κ).abs_le n k
      gcongr
    have e2 := jbL2_wsel_le (c := c) (m := m) (c.P k) k
    have e3 := hc.overlap_ub k
    have e4 : (h ^ m * cs.K) * jbL2 (c.P k) (fun n => c.wsel m n k) ≤
        ε * jbL2 (c.P k) (fun n => c.phi1 h n k) := by
      have e5 : jbL2 (c.P k) (fun n => c.wsel m n k) ≤ cs.C4 * jbL2 (c.P k) (fun n => c.phi1 h n k) :=
        e2.trans e3
      have e6 : 0 ≤ h ^ m * cs.K := by positivity
      refine (mul_le_mul_of_nonneg_left e5 e6).trans (le_of_eq ?_)
      rw [hε]; ring
    exact e1.trans e4
  -- hosts restricted to `P_k`
  have hs : jbL2 (c.P k) (fun n => c.σ0 k * c.phi0 h n k - U (c.row n) k) ≤ δ := by
    have e : (fun n => c.σ0 k * c.phi0 h n k - U (c.row n) k) =
        fun n => c.host0 (c.row n) k - U (c.row n) k := by
      funext n; rw [← hc.host0_eq n k]; rfl
    rw [e]
    exact (jbL2_comp_le (c.P k) c.row c.row_injective (fun i => c.host0 i k - U i k)).trans
      (hc.host0_col k)
  have ht : jbL2 (c.P k) (fun n => c.σ1 k * c.phi1 h n k - U (c.row n) k) ≤ δ := by
    have e : (fun n => c.σ1 k * c.phi1 h n k - U (c.row n) k) =
        fun n => c.host1 (c.row n) k - U (c.row n) k := by
      funext n; rw [← hc.host1_eq n k]; rfl
    rw [e]
    refine (jbL2_comp_le (c.P k) c.row c.row_injective (fun i => c.host1 i k - U i k)).trans
      ((hc.host1_col k).trans ?_)
    have := mul_log_inv_le_one hh0
    calc cs.C * h ^ (m + 1) * Real.log (1 / h) = cs.C * h ^ m * (h * Real.log (1 / h)) := by ring
      _ ≤ cs.C * h ^ m * 1 := by gcongr
      _ = δ := by rw [hδ]; ring
  have key := jb_ratio (c.P k) (fun n => U (c.row n) k) (fun n => c.phi0 h n k)
    (fun n => c.phi1 h n k) (c0 := cs.c0) (δ := δ) (ε := ε) (s := c.σ0 k) (t := c.σ1 k)
    (hc.overlap_lb k) (by linarith) hε0 (by linarith) hdiff hs ht
  refine ⟨key.1, key.2.trans ?_⟩
  have hd : cs.c0 / 2 ≤ cs.c0 - δ := by linarith
  have hd0 : 0 < cs.c0 - δ := by linarith
  have e5 : 2 * δ / (cs.c0 - δ) ≤ 4 * δ / cs.c0 := by
    rw [div_le_div_iff₀ hd0 hc0]
    nlinarith
  have e6 : (ε + 2 * δ / (cs.c0 - δ)) / (1 - ε) ≤ 2 * (ε + 4 * δ / cs.c0) := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ ε + 4 * δ / cs.c0 := by positivity
    nlinarith
  refine e6.trans (le_of_eq ?_)
  rw [hε, hδ]; ring

theorem rho_le_five (hKC : cs.K * cs.C4 * h ^ m ≤ 1 / 2) (hC : cs.C * h ^ m ≤ cs.c0 / 2) :
    2 * (cs.K * cs.C4 + 4 * cs.C / cs.c0) * h ^ m ≤ 5 := by
  have hc0 := cs.c0_pos
  have e : 2 * (cs.K * cs.C4 + 4 * cs.C / cs.c0) * h ^ m =
      2 * (cs.K * cs.C4 * h ^ m) + 8 * (cs.C * h ^ m) / cs.c0 := by ring
  rw [e]
  have : 8 * (cs.C * h ^ m) / cs.c0 ≤ 4 := by
    rw [div_le_iff₀ hc0]; nlinarith
  linarith

/-- Step 3 (carriers): `‖Y'‖` and `‖Ỹ'‖` are bounded independently of the number of columns. -/
theorem chart_carriers (hc : c.Ok cs m h U) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hk : h * cs.K * cs.ωmax ≤ 1 / 2) (hH : ‖c.H1 h‖ ≤ 2) :
    ‖c.Y'‖ ≤ 2 * cs.K * (2 + cs.CE) ∧
      ‖c.Yt'‖ ≤ cs.K * ((cs.ωmax + 1) * (2 * cs.K * (2 + cs.CE)) + cs.CE) := by
  have hF : c.H1 h = c.A1 ⊙ c.Y' + h • (c.B1 ⊙ c.Yt') := by
    ext n k
    simp only [H1_apply, phi1_apply, Y', Yt', Matrix.add_apply, Matrix.smul_apply, hadamard_apply,
      of_apply, smul_eq_mul]
    ring
  have ht12 : ∀ n k, c.t12 n k ≠ 0 := fun n k => by
    have h1 := hc.t12_lb n k
    have h2 := cs.cT_pos
    intro h0
    rw [h0] at h1
    simp at h1
    linarith
  have hα : ∀ n k, jbAlpha c.A1 c.B1 c.t11 c.t12 h n k ≠ 0 := fun n k =>
    ne_of_gt (lt_of_lt_of_le cs.cα_pos (hc.α_lb n k))
  have hk1 : h * cs.K * cs.ωmax < 1 := by linarith
  have hK0 := cs.K_nonneg
  have hω0 := cs.ωmax_pos.le
  by_cases hτ : c.τ = true
  · have hT : ∀ n k, c.ω n * Ysh (fun k => c.σ1 k * c.yext k) c.Y' n k =
        c.t11 n k * c.Y' n k + c.t12 n k * c.Yt' n k := by
      intro n k
      have := hc.transfer n k
      simp only [Chart.shifted, hτ, if_true, of_apply] at this
      have e : Ysh (fun k => c.σ1 k * c.yext k) c.Y' n k = c.σ1 k * Ysh c.yext c.y n k :=
        Ysh_scale c.σ1 c.yext c.y n k
      rw [e]
      simp only [Y', Yt', of_apply]
      linear_combination (c.σ1 k) * this
    have g := jb_glue c.Y' c.Yt' (c.H1 h) c.A1 c.B1 c.t11 c.t12 c.ω (fun k => c.σ1 k * c.yext k)
      hc.ω_pos hT hF ht12 hα hc.schur_inv_α hc.schur_B hc.schur_inv_t12 hc.schur_t11 hh0 hk1
    have hE : ‖extRow c.ω (fun k => c.σ1 k * c.yext k)‖ ≤ cs.CE :=
      norm_extRow_le _ _ cs.CE_nonneg fun n hn => by
        have := hc.ext_row n (fun _ => hn) (fun h' => absurd hτ (by simp [h']))
        have e : (fun k => c.ω n * (c.σ1 k * c.yext k)) = fun k => c.ω n * c.σ1 k * c.yext k := by
          funext k; ring
        rw [e]; exact this
    exact glue_arith hK0 hω0 hh0 hh1 hk hH hE (norm_nonneg _) g.1 g.2
  · have hτf : c.τ = false := by simpa using hτ
    have hT : ∀ n k, c.ω n * YshRev (fun k => c.σ1 k * c.yext k) c.Y' n k =
        c.t11 n k * c.Y' n k + c.t12 n k * c.Yt' n k := by
      intro n k
      have := hc.transfer n k
      simp only [Chart.shifted, hτf, Bool.false_eq_true, ite_false, of_apply] at this
      have e : YshRev (fun k => c.σ1 k * c.yext k) c.Y' n k = c.σ1 k * YshRev c.yext c.y n k :=
        YshRev_scale c.σ1 c.yext c.y n k
      rw [e]
      simp only [Y', Yt', of_apply]
      linear_combination (c.σ1 k) * this
    have g := jb_glue_rev c.Y' c.Yt' (c.H1 h) c.A1 c.B1 c.t11 c.t12 c.ω (fun k => c.σ1 k * c.yext k)
      hc.ω_pos hT hF ht12 hα hc.schur_inv_α hc.schur_B hc.schur_inv_t12 hc.schur_t11 hh0 hk1
    have hE : ‖extRowRev c.ω (fun k => c.σ1 k * c.yext k)‖ ≤ cs.CE :=
      norm_extRowRev_le _ _ cs.CE_nonneg fun n hn => by
        have := hc.ext_row n (fun h' => absurd h' (by simp [hτf])) (fun _ => hn)
        have e : (fun k => c.ω n * (c.σ1 k * c.yext k)) = fun k => c.ω n * c.σ1 k * c.yext k := by
          funext k; ring
        rw [e]; exact this
    exact glue_arith hK0 hω0 hh0 hh1 hk hH hE (norm_nonneg _) g.1 g.2

/-- The constant of one chart (Step 4): `C₁ = 2 C_ρ + 6 K (B_Y + B_Ỹ)` with `C_ρ = 2 (K C₄ + 4 C / c₀)`,
`B_Y = 2 K (2 + C_E)`, `B_Ỹ = K ((ω_max + 1) B_Y + C_E)`. -/
noncomputable def chartConst (cs : OneStepConsts) : ℝ :=
  2 * (2 * (cs.K * cs.C4 + 4 * cs.C / cs.c0)) +
    6 * cs.K * (2 * cs.K * (2 + cs.CE) + cs.K * ((cs.ωmax + 1) * (2 * cs.K * (2 + cs.CE)) + cs.CE))

theorem chartConst_nonneg (cs : OneStepConsts) : 0 ≤ chartConst cs := by
  have := cs.c0_pos
  have := cs.K_nonneg
  have := cs.C4_nonneg
  have := cs.C_nonneg
  have := cs.CE_nonneg
  have := cs.ωmax_pos
  unfold chartConst
  positivity

/-- Step 4 (one chart): `‖H^{[m]}_c - H^{[m+1]}_c‖ ≤ C₁ h^m`. -/
theorem chart_diff (hc : c.Ok cs m h U) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (h2 : cs.K * cs.C4 * h ^ m ≤ 1 / 2) (h3 : cs.C * h ^ m ≤ cs.c0 / 2)
    (hk : h * cs.K * cs.ωmax ≤ 1 / 2) (hH : ‖c.H1 h‖ ≤ 2) :
    ‖c.H0 h - c.H1 h‖ ≤ chartConst cs * h ^ m := by
  have hhm : 0 < h ^ m := pow_pos hh0 m
  have hK0 := cs.K_nonneg
  set Cρ : ℝ := 2 * (cs.K * cs.C4 + 4 * cs.C / cs.c0) with hCρ
  have hCρ5 : Cρ * h ^ m ≤ 5 := rho_le_five h2 h3
  have hCρ0 : 0 ≤ Cρ := by
    have := cs.c0_pos; have := cs.C4_nonneg; have := cs.C_nonneg
    rw [hCρ]; positivity
  -- the scalars
  have hρ : ∀ k : cols, ∃ ρ : ℝ, c.σ0 k = (1 + ρ) * c.σ1 k ∧ |ρ| ≤ Cρ * h ^ m := fun k => by
    obtain ⟨h0, h1⟩ := chart_ratio hc hh0 hh1 h2 h3 k
    refine ⟨c.σ0 k / c.σ1 k - 1, ?_, h1⟩
    field_simp; ring
  choose ρ hρ0 hρ1 using hρ
  have hρ5 : ∀ k, |ρ k| ≤ 5 := fun k => (hρ1 k).trans hCρ5
  obtain ⟨hY, hYt⟩ := chart_carriers hc hh0.le hh1 hk hH
  set W : Matrix (Fin R) cols ℝ := Matrix.of fun n k => c.σ1 k * c.wsel m n k with hW
  have hWn : ‖W‖ ≤ 2 * cs.K * (2 + cs.CE) +
      cs.K * ((cs.ωmax + 1) * (2 * cs.K * (2 + cs.CE)) + cs.CE) := by
    have h1 : 0 ≤ ‖c.Y'‖ := norm_nonneg _
    have h2' : 0 ≤ ‖c.Yt'‖ := norm_nonneg _
    have e : W = c.Y' ∨ W = c.Yt' := by
      by_cases hm : m % 2 = 0
      · left; ext n k; simp [hW, wsel, Y', hm]
      · right; ext n k; simp [hW, wsel, Yt', hm]
    rcases e with e | e <;> rw [e] <;> linarith
  have hid : c.H0 h - c.H1 h = c.H1 h * diagonal ρ -
      h ^ m • ((c.κ ⊙ W) * diagonal (fun k => 1 + ρ k)) := by
    ext n k
    have hd := phi_diff hc n k
    simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.smul_apply, hadamard_apply, hW, of_apply,
      smul_eq_mul, H0_apply, H1_apply]
    have e0 := hρ0 k
    have ed : c.phi0 h n k = c.phi1 h n k - h ^ m * c.κ n k * c.wsel m n k := by linarith
    rw [e0, ed]; ring
  have hD1 : ‖(diagonal ρ : Matrix cols cols ℝ)‖ ≤ Cρ * h ^ m :=
    FormalResearch.MatrixAnalysis.jop_norm_diagonal_le ρ (by positivity) hρ1
  have hD2 : ‖(diagonal (fun k => 1 + ρ k) : Matrix cols cols ℝ)‖ ≤ 6 :=
    FormalResearch.MatrixAnalysis.jop_norm_diagonal_le _ (by norm_num) fun k => by
      have := hρ5 k
      calc |1 + ρ k| ≤ |1| + |ρ k| := abs_add_le _ _
        _ ≤ 6 := by simp; linarith
  rw [hid]
  have t1 : ‖c.H1 h * diagonal ρ‖ ≤ 2 * (Cρ * h ^ m) :=
    (l2_opNorm_mul _ _).trans (mul_le_mul hH hD1 (norm_nonneg _) (by norm_num))
  set Bd : ℝ := 2 * cs.K * (2 + cs.CE) +
      cs.K * ((cs.ωmax + 1) * (2 * cs.K * (2 + cs.CE)) + cs.CE) with hBd
  have t2 : ‖h ^ m • ((c.κ ⊙ W) * diagonal (fun k => 1 + ρ k))‖ ≤ h ^ m * (cs.K * Bd * 6) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hh0 m)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_pos hh0 m).le
    refine (l2_opNorm_mul _ _).trans ?_
    have h1 := hc.schur_κ.apply_le W
    have h2 : ‖c.κ ⊙ W‖ ≤ cs.K * Bd := h1.trans (mul_le_mul_of_nonneg_left hWn hK0)
    have h4 : 0 ≤ cs.K * Bd := (norm_nonneg _).trans h2
    exact mul_le_mul h2 hD2 (norm_nonneg _) h4
  have e : chartConst cs * h ^ m = 2 * (Cρ * h ^ m) + h ^ m * (cs.K * Bd * 6) := by
    unfold chartConst; rw [hCρ, hBd]; ring
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add t1 t2)

end Chart

end FormalResearch.JB
