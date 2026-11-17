module

public import FormalResearch.Special.DiscreteAiryKappaChart
public import FormalResearch.Special.HermiteAiryEdge

/-!
# The Hermite Airy edge with the chart data exported

`hermite_airy_edge` (`HermiteAiryEdge`) gives `φ_{-k}(x) = κ g Ai(X_k) + μ g Bi(X_k) + O(δ³)` but hides the chart constants
(`g_min ≤ g ≤ g_max`, lattice gaps, `X_m ∈ [0, c₂δ]`).  `hermite_kappa_edge` is the same statement with these exported, obtained from
`kc_turn_full` (`DiscreteAiryKappaChart`) applied to the Hermite datum `u = (√(-q))⁻¹`, `A = √(-q/2)`, `c₀ = -1`, `E = 0`.
It is what the order bounds on `κ` (`hermite_kappa_order`, `HermiteKappaLower`) are built on.

**Claim class: proved.**  `κ` itself is not identified here.
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **The Airy-edge conclusion with chart data** for the reflected Hermite chain `Y_k = φ_{-k}(x)` at `δ³ = 2/x²`:
window indices `J < N`, `J ≤ m ≤ N ≤ -1` (`m` at the turn, `q_m ∈ [-1, -1 + δ³)`), `g ∈ [g_min, g_max]` and lattice gaps
`X_{k+1} - X_k ∈ [c₁δ, c₂δ]` on the window, `|g_{k+1} - g_k| ≤ L_g δ³`, `X_m ∈ [0, c₂δ]`, `c₂ δ ≤ 1/8`,
`|μ| ≤ C_μ √(x²+2) e^{-ξ₀/δ³}/δ` and
`|φ_{-k}(x) - (κ g_k Ai(X_k) + μ g_k Bi(X_k))| ≤ C δ³ (|κ| airyWt(X_k) + |μ| airyBiWt(X_k))` for `k ∈ [J, N+1]`. -/
def HkEdge (r C Cmu ξ0 gmax gmin c1 c2 Lg x δ : ℝ) (J m N : ℤ) (κ μ : ℝ) : Prop :=
  J < N ∧ J ≤ m ∧ m ≤ N ∧ N ≤ -1 ∧
    (∀ k ∈ Finset.Icc J (N + 1), dalQ (-δ ^ 3 / 2) δ k ∈ Set.Icc (-1 - r) (-1 + r)) ∧
    dalQ (-δ ^ 3 / 2) δ J < -1 - r + δ ^ 3 ∧
    -1 ≤ dalQ (-δ ^ 3 / 2) δ m ∧ dalQ (-δ ^ 3 / 2) δ m < -1 + δ ^ 3 ∧
    -1 + r / 4 ≤ dalQ (-δ ^ 3 / 2) δ N ∧ dalQ (-δ ^ 3 / 2) δ (N + 1) ≤ -1 + r / 2 ∧
    (∀ k ∈ Finset.Icc J (N + 1), gmin ≤ langerAmp hmU hmA (-1) (dalQ (-δ ^ 3 / 2) δ k) ∧
      langerAmp hmU hmA (-1) (dalQ (-δ ^ 3 / 2) δ k) ≤ gmax) ∧
    (∀ k ∈ Finset.Icc J N, c1 * δ ≤ turnX hmU (-1) (-δ ^ 3 / 2) δ (k + 1) - turnX hmU (-1) (-δ ^ 3 / 2) δ k ∧
      turnX hmU (-1) (-δ ^ 3 / 2) δ (k + 1) - turnX hmU (-1) (-δ ^ 3 / 2) δ k ≤ c2 * δ) ∧
    (∀ k ∈ Finset.Icc J N, |langerAmp hmU hmA (-1) (dalQ (-δ ^ 3 / 2) δ (k + 1)) -
      langerAmp hmU hmA (-1) (dalQ (-δ ^ 3 / 2) δ k)| ≤ Lg * δ ^ 3) ∧
    (0 ≤ turnX hmU (-1) (-δ ^ 3 / 2) δ m ∧ turnX hmU (-1) (-δ ^ 3 / 2) δ m ≤ c2 * δ) ∧ c2 * δ ≤ 1 / 8 ∧
    |μ| ≤ Cmu * √(x ^ 2 + 2) * Real.exp (-ξ0 / δ ^ 3) / δ ∧
    ∀ k ∈ Finset.Icc J (N + 1),
      |hermitePsi (-k) x -
          (κ * daoPhi (fun k => langerAmp hmU hmA (-1) (dalQ (-δ ^ 3 / 2) δ k))
              (turnX hmU (-1) (-δ ^ 3 / 2) δ) k +
            μ * daoPsi (fun k => langerAmp hmU hmA (-1) (dalQ (-δ ^ 3 / 2) δ k))
              (turnX hmU (-1) (-δ ^ 3 / 2) δ) k)| ≤
        C * δ ^ 3 * (|κ| * airyWt (turnX hmU (-1) (-δ ^ 3 / 2) δ k) +
          |μ| * airyBiWt (turnX hmU (-1) (-δ ^ 3 / 2) δ k))

/-- **Hermite Airy edge with chart data**: absolute constants such that for every `x > 0`, `δ ≤ δ₀`, `δ³ = 2/x²` (`S = x²/2`) there
are `J, m, N, κ, μ` with `HkEdge`. -/
theorem hermite_kappa_edge :
    ∃ r δ0 C Cmu ξ0 gmax gmin c1 c2 Lg : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmin ∧
      gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧ 0 ≤ Lg ∧
      ∀ x δ : ℝ, 0 < x → 0 < δ → δ ≤ δ0 → δ ^ 3 = 2 / x ^ 2 →
        ∃ (J m N : ℤ) (κ μ : ℝ), HkEdge r C Cmu ξ0 gmax gmin c1 c2 Lg x δ J m N κ μ := by
  have hmem : (-1 : ℝ) ∈ Set.Iio (0 : ℝ) := by norm_num
  have h3 : ContDiffAt ℝ 3 hmU (-1) := (hmU_cd.contDiffAt (Iio_mem_nhds hmem))
  have h2 : ContDiffAt ℝ 2 hmA (-1) := ((hmA_cd.contDiffAt (Iio_mem_nhds hmem)).of_le (by norm_num))
  have hA0 : 0 < hmA (-1) := by unfold hmA; exact Real.sqrt_pos.2 (by norm_num)
  have hu' : 0 < deriv hmU (-1) := by rw [hasDerivAt_hmU_neg_one.deriv]; norm_num
  obtain ⟨r, δ0, C, Cmu, ξ0, gmax, gmin, c1, c2, Lg, hr, hrr0, hδ0, hδ01, hC, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, hLg0, H⟩ :=
    kc_turn_full h3 hmU_neg_one hu' h2 hA0 (r0 := 1 / 2) (by norm_num) 0 le_rfl
  refine ⟨r, δ0, C, Cmu, ξ0, gmax, gmin, c1, c2, Lg, hr, hrr0, hδ0, hC, hCmu, hξ0, hgmin, hgg, hc1, hc12, hLg0, ?_⟩
  intro x δ hx hδ hδδ0 hδx
  obtain ⟨J, m, N, hJN, hJm, hmN, hwin, hqJ1, hqJ2, hqm1, hqm2, hqN, hqN1, hg, hXm, hgl, hgap, ⟨hX0, hX1⟩, hXN, hLgb,
    hc2δ, hcoef⟩ := H δ (-δ ^ 3 / 2) hδ hδδ0
  have hDF := hcoef (hmCoefA δ) (hmCoefC δ)
    (fun k _ => by simp [hmCoefA])
    (fun k _ => by simp [hmCoefC])
  have hδ3 : 0 < δ ^ 3 := by positivity
  have hNneg : N ≤ -1 := by
    by_contra hcon
    have h0 : (0 : ℝ) ≤ N := by exact_mod_cast (by omega : (0 : ℤ) ≤ N)
    have : -1 + r / 2 ≥ dalQ (-δ ^ 3 / 2) δ (N + 1) := hqN1
    simp only [dalQ] at this
    push_cast at this
    nlinarith [mul_nonneg h0 hδ3.le]
  have hNlow : ((-N : ℤ) : ℝ) ≤ x ^ 2 / 2 := by
    have h := hqN
    simp only [dalQ] at h
    have hx2 : δ ^ 3 * (x ^ 2 / 2) = 1 := by rw [hδx]; field_simp
    push_cast
    nlinarith
  have hrows : ∀ k ∈ Finset.Icc (J + 1) N, jac (hmCoefA δ) (hmCoefC δ) (hmY x) k = 0 := fun k hk =>
    hermite_row hx hδx k (by rw [Finset.mem_Icc] at hk; omega)
  have hYN : |hmY x N| ≤ √(x ^ 2 + 2) := by
    unfold hmY
    have hN' : 0 ≤ -N := by omega
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hN'
    rw [hn, hermitePsi_natCast]
    refine (abs_hermitePhi_le n x).trans (Real.sqrt_le_sqrt ?_)
    have : (n : ℝ) ≤ x ^ 2 / 2 := by
      have : ((n : ℤ) : ℝ) = ((-N : ℤ) : ℝ) := by rw [hn]
      push_cast at this hNlow ⊢
      linarith
    linarith
  have hYN1 : |hmY x (N + 1)| ≤ √(x ^ 2 + 2) := by
    unfold hmY
    have hN' : 0 ≤ -(N + 1) := by omega
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hN'
    rw [hn, hermitePsi_natCast]
    refine (abs_hermitePhi_le n x).trans (Real.sqrt_le_sqrt ?_)
    have : (n : ℝ) ≤ x ^ 2 / 2 := by
      have h1 : ((n : ℤ) : ℝ) = ((-(N + 1) : ℤ) : ℝ) := by rw [hn]
      push_cast at h1 hNlow ⊢
      linarith
    linarith
  obtain ⟨κ, μ, hμ, hY⟩ := DaiFull.pointwise hDF (hmY x) (√(x ^ 2 + 2)) hrows hYN hYN1
  have hxi : ξ0 / δ ^ 3 ≤ airyXi (turnX hmU (-1) (-δ ^ 3 / 2) δ N) := hDF.1
  have hμ2 : |μ| ≤ Cmu * √(x ^ 2 + 2) * Real.exp (-ξ0 / δ ^ 3) / δ := by
    refine hμ.trans ?_
    gcongr
    have e : -ξ0 / δ ^ 3 = -(ξ0 / δ ^ 3) := neg_div _ _
    rw [e]
    linarith
  exact ⟨J, m, N, κ, μ, hJN, hJm, hmN, hNneg, hwin, hqJ2, hqm1, hqm2, hqN, hqN1,
    fun k hk => ⟨hgl k hk, (abs_le.1 (hg k hk)).2⟩, hgap, hLgb, ⟨hX0, hX1⟩, hc2δ, hμ2, hY⟩

/-- info: 'FormalResearch.Special.hermite_kappa_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hermite_kappa_edge

end FormalResearch.Special
