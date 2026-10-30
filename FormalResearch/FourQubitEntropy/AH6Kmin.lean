import FormalResearch.FourQubitEntropy.AH6Jensen

/-!
# The kernel minorant `K(e) ≥ k₀/L(e)` (`eq:seven-joint-kernel-jensen`)

Let `P` be the Newton interpolant of `g = negMulLog (·/8)` on the double nodes `n₁ n₂ n₃`, `q = (e-n₁)(e-n₂)(e-n₃)`,
`k₀ = (P(e₀) - g(e₀))/q(e₀)²`, `k₁ = (P'(e₀) - g'(e₀))/q(e₀)² - 2 k₀ q'(e₀)/q(e₀)`, `γ = -k₁/k₀`, `L(e) = 1 + γ(e-e₀)`.
Then `k₀ > 0`, `0 ≤ γ e₀ ≤ 1` and `k₀ q(e)² ≤ (P(e) - g(e)) L(e)` for all `e > 0`
(`kmin`).  The proof: `P - g = q² K̃` (`hermite_stieltjes`), the Jensen bound with the mean `c` (`jensen_kint`), and
`c = γ` because `e ↦ K̃(e)(1 + c(e-e₀)) - K̃(e₀)` is nonnegative with a zero at `e₀` (Fermat), so its derivative
`K̃'(e₀) + c K̃(e₀)` vanishes; `K̃'(e₀)` is computed from `K̃ = (P - g)/q²` near `e₀`.
-/

namespace FormalResearch.FourQubitEntropy.AH6

open MeasureTheory intervalIntegral Set Filter Topology

section

variable {n1 n2 n3 i21 i31 i32 : ℝ}

/-- The Newton interpolant of `g` as a function of `e`. -/
noncomputable def Pfun (n1 n2 n3 i21 i31 i32 : ℝ) (e : ℝ) : ℝ :=
  newtonP n1 n2 n3 i21 i31 i32 (Real.negMulLog (n1 / 8)) (-(Real.log (n1 / 8) + 1) / 8)
    (Real.negMulLog (n2 / 8)) (-(Real.log (n2 / 8) + 1) / 8)
    (Real.negMulLog (n3 / 8)) (-(Real.log (n3 / 8) + 1) / 8) e

theorem kmin (hn1 : 0 < n1) (hn2 : 0 < n2) (hn3 : 0 < n3)
    (h21 : (n2 - n1) * i21 = 1) (h31 : (n3 - n1) * i31 = 1) (h32 : (n3 - n2) * i32 = 1)
    {e0 p1 q1 : ℝ} (he0 : 0 < e0) (hq0 : (e0 - n1) * (e0 - n2) * (e0 - n3) ≠ 0)
    (hP' : HasDerivAt (Pfun n1 n2 n3 i21 i31 i32) p1 e0)
    (hq1 : HasDerivAt (fun e => (e - n1) * (e - n2) * (e - n3)) q1 e0) :
    let q0 := (e0 - n1) * (e0 - n2) * (e0 - n3)
    let g0 := Real.negMulLog (e0 / 8)
    let g1 := -(Real.log (e0 / 8) + 1) / 8
    let k0 := (Pfun n1 n2 n3 i21 i31 i32 e0 - g0) / q0 ^ 2
    let k1 := (p1 - g1) / q0 ^ 2 - 2 * (k0 * (q1 / q0))
    let γ := -(k1 / k0)
    0 < k0 ∧ 0 ≤ γ * e0 ∧ γ * e0 ≤ 1 ∧
      ∀ e : ℝ, 0 < e → k0 * ((e - n1) * (e - n2) * (e - n3)) ^ 2 ≤
        (Pfun n1 n2 n3 i21 i31 i32 e - Real.negMulLog (e / 8)) * (1 + γ * (e - e0)) := by
  intro q0 g0 g1 k0 k1 γ
  obtain ⟨hK0, c, hc0, hce, hJ⟩ := jensen_kint hn1 hn2 hn3 he0
  have hst : ∀ e : ℝ, 0 < e → Pfun n1 n2 n3 i21 i31 i32 e =
      Real.negMulLog (e / 8) + ((e - n1) * (e - n2) * (e - n3)) ^ 2 * Kint n1 n2 n3 e :=
    fun e he => hermite_stieltjes hn1 hn2 hn3 h21 h31 h32 he
  have hk0 : k0 = Kint n1 n2 n3 e0 := by
    show (Pfun n1 n2 n3 i21 i31 i32 e0 - Real.negMulLog (e0 / 8)) / q0 ^ 2 = _
    have hP0 : Pfun n1 n2 n3 i21 i31 i32 e0 - Real.negMulLog (e0 / 8) = q0 ^ 2 * Kint n1 n2 n3 e0 := by
      rw [hst e0 he0]; ring
    rw [hP0]
    exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hq0)
  -- Fermat: c = γ
  set q : ℝ → ℝ := fun e => (e - n1) * (e - n2) * (e - n3) with hq
  have hg : HasDerivAt (fun e => Real.negMulLog (e / 8)) g1 e0 := by
    have h := (Real.hasDerivAt_negMulLog (show e0 / 8 ≠ 0 by positivity)).comp e0
      ((hasDerivAt_id e0).div_const 8)
    refine HasDerivAt.congr_deriv h ?_
    show (-Real.log (e0 / 8) - 1) * (1 / 8) = -(Real.log (e0 / 8) + 1) / 8
    ring
  have hqe : q0 ≠ 0 := hq0
  have hKd : HasDerivAt (fun e => (Pfun n1 n2 n3 i21 i31 i32 e - Real.negMulLog (e / 8)) / (q e) ^ 2)
      (((p1 - g1) * q0 ^ 2 - (Pfun n1 n2 n3 i21 i31 i32 e0 - g0) * (2 * q0 * q1)) / (q0 ^ 2) ^ 2) e0 := by
    have hd := hP'.sub hg
    have hp := (hq1.pow 2)
    have := hd.div hp (pow_ne_zero 2 hqe)
    refine HasDerivAt.congr_deriv this ?_
    simp only [Pi.pow_apply, Pi.sub_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    first | rfl | ring
  have hev : (fun e => (Pfun n1 n2 n3 i21 i31 i32 e - Real.negMulLog (e / 8)) / (q e) ^ 2) =ᶠ[𝓝 e0]
      Kint n1 n2 n3 := by
    have h1 : ∀ᶠ e in 𝓝 e0, 0 < e := Ioi_mem_nhds he0
    have hqc : ContinuousAt q e0 := by simp only [hq]; fun_prop
    have h2 : ∀ᶠ e in 𝓝 e0, q e ≠ 0 := hqc.eventually_ne hqe
    filter_upwards [h1, h2] with e he hqe'
    rw [hst e he]
    field_simp
    ring
  have hKd' : HasDerivAt (Kint n1 n2 n3)
      (((p1 - g1) * q0 ^ 2 - (Pfun n1 n2 n3 i21 i31 i32 e0 - g0) * (2 * q0 * q1)) / (q0 ^ 2) ^ 2) e0 :=
    hKd.congr_of_eventuallyEq hev.symm
  have hm : HasDerivAt (fun e => Kint n1 n2 n3 e * (1 + c * (e - e0)) - Kint n1 n2 n3 e0)
      (((p1 - g1) * q0 ^ 2 - (Pfun n1 n2 n3 i21 i31 i32 e0 - g0) * (2 * q0 * q1)) / (q0 ^ 2) ^ 2 +
        Kint n1 n2 n3 e0 * c) e0 := by
    have h2 : HasDerivAt (fun e => 1 + c * (e - e0)) c e0 := by
      have := (((hasDerivAt_id e0).sub_const e0).const_mul c).const_add 1
      simpa using this
    have := (hKd'.mul h2).sub_const (Kint n1 n2 n3 e0)
    refine HasDerivAt.congr_deriv this ?_
    simp
  have hmin : IsLocalMin (fun e => Kint n1 n2 n3 e * (1 + c * (e - e0)) - Kint n1 n2 n3 e0) e0 := by
    filter_upwards [Ioi_mem_nhds he0] with e he
    have := hJ e he
    simp only [sub_self, mul_zero, add_zero, mul_one, sub_nonneg]
    linarith
  have hfer := hmin.hasDerivAt_eq_zero hm
  have hcg : c = γ := by
    have hk0' : k0 ≠ 0 := by rw [hk0]; exact hK0.ne'
    have : γ = -(k1 / k0) := rfl
    have hk1 : k1 = ((p1 - g1) * q0 ^ 2 - (Pfun n1 n2 n3 i21 i31 i32 e0 - g0) * (2 * q0 * q1)) /
        (q0 ^ 2) ^ 2 := by
      show (p1 - g1) / q0 ^ 2 - 2 * (k0 * (q1 / q0)) = _
      have hk0def : k0 = (Pfun n1 n2 n3 i21 i31 i32 e0 - g0) / q0 ^ 2 := rfl
      rw [hk0def]
      field_simp
    rw [← hk1, ← hk0] at hfer
    rw [this]
    field_simp
    linarith
  rw [← hcg]
  refine ⟨by rw [hk0]; exact hK0, ?_⟩
  refine ⟨mul_nonneg hc0 he0.le, hce, ?_⟩
  intro e he
  have hJ' := hJ e he
  have hst' := hst e he
  have hqq : 0 ≤ ((e - n1) * (e - n2) * (e - n3)) ^ 2 := sq_nonneg _
  have hdiff : Pfun n1 n2 n3 i21 i31 i32 e - Real.negMulLog (e / 8) =
      ((e - n1) * (e - n2) * (e - n3)) ^ 2 * Kint n1 n2 n3 e := by rw [hst']; ring
  rw [hdiff]
  calc k0 * ((e - n1) * (e - n2) * (e - n3)) ^ 2
      = ((e - n1) * (e - n2) * (e - n3)) ^ 2 * Kint n1 n2 n3 e0 := by rw [hk0]; ring
    _ ≤ ((e - n1) * (e - n2) * (e - n3)) ^ 2 * (Kint n1 n2 n3 e * (1 + c * (e - e0))) :=
        mul_le_mul_of_nonneg_left hJ' hqq
    _ = _ := by ring

end

end FormalResearch.FourQubitEntropy.AH6
