module

public import FormalResearch.SignUncertainty.GenRationalO6Family
public import FormalResearch.SignUncertainty.CeDualFloors

/-!
# Dual-line positivity for generalized rational-Airy seeds (`lem:ce-dual-line`)

Source: `CFT/sign_uncertainty/paper/ce_lift_proofs.tex`, Lemma `lem:ce-dual-line`.

* `ce_dual_line`: for `D_c = X + ε_c Z_c` with `X ∈ ℛ_Ai^gen` satisfying `eq:ce-dual-floors` and
  `ℒ_y(X) ≥ 0` on `y > 0`, and `Z_c` a uniformly bounded finite linear combination in `ℛ_Ai^gen`
  having positive mass and a positive floor on `J = [x₀/3, 2B]`, the weighted dual symbol
  `W_{D_c}(w) = M_ψ(w) (D_c)̃(i c_s w)` satisfies all dual-line positivity, small-`x` / tail floors,
  `hA1_D` local variation, and `hA2_D` strip bounds needed by `PreEdgeTangencyData` uniformly for large `c`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- **`lem:ce-dual-line` (`ce_lift_proofs.tex`):** uniform dual-line positivity, small-`x` / tail
floors, `hA1_D` local variation, and `hA2_D` strip bounds for `W_{D_c}` when `D_c = X + ε_c Z_c`
is formed from a floor-satisfying `X ∈ ℛ_Ai^gen` and a uniformly bounded finite linear combination
family `Z_c` in `ℛ_Ai^gen` with positive mass and positive `J`-floor. -/
theorem ce_dual_line {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁)
    (hmass : ∫ u : ℝ, (F (u : ℂ)).re = 0)
    (hnonneg : ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => (F (u : ℂ)).re) y)
    {ι : Type*} (s : Finset ι) (B : ι → ℂ → ℂ) (b₀₀ b₁₁ : ι → ℝ)
    (hB : ∀ i ∈ s, HasGenRationalAiryCoeffs (B i) (b₀₀ i) (b₁₁ i))
    (α : ι → ℝ → ℝ) (R c_min m_Z z₀ : ℝ) (hR : 0 ≤ R) (hc_min : 2 ≤ c_min)
    (hm_Z : 0 < m_Z) (hz₀ : 0 < z₀)
    (hα : ∀ i ∈ s, ∀ c : ℝ, c_min ≤ c → |α i c| ≤ R)
    (hZ_mass : ∀ c : ℝ, c_min ≤ c → m_Z ≤ ∫ u : ℝ, ∑ i ∈ s, α i c * (B i (u : ℂ)).re)
    {x₀ B₀ c₁' d₀ : ℝ} (hx₀ : 0 < x₀) (hx₀B : x₀ < B₀) (hc₁' : 0 < c₁') (hd₀ : 0 < d₀)
    (hX_small : ∀ x ∈ Icc (0 : ℝ) x₀,
      c₁' * Real.sqrt x ≤ (airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re)
    (hX_tail : ∀ x : ℝ, B₀ / 2 ≤ x → d₀ * (1 + x) ^ (-(5 / 2 : ℝ)) ≤
      (airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re)
    (hZ_J : ∀ c : ℝ, c_min ≤ c → ∀ x ∈ Icc (x₀ / 3) (2 * B₀), z₀ ≤
      (airyTwistedLaplaceC (fun u => ∑ i ∈ s, α i c * (B i (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re)
    {K : ℝ} (hK : 1 ≤ K) {m : ℕ} (hm : 1 ≤ m) :
    let X : ℝ → ℝ := fun u => (F (u : ℂ)).re
    let Z : ℝ → ℝ → ℝ := fun c u => ∑ i ∈ s, α i c * (B i (u : ℂ)).re
    let D : ℝ → ℝ → ℝ := fun c u => X u + liftEps c * Z c u
    let W_D : ℝ → ℂ → ℂ := fun c w => liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m w
    ∃ c₀ M Λ Λ_add_max b c_J d_tail K_D : ℝ,
      c_min ≤ c₀ ∧ 1 ≤ M ∧ 1 ≤ Λ ∧ 0 ≤ Λ_add_max ∧ 0 < b ∧ 0 < c_J ∧ 0 < d_tail ∧ 0 ≤ K_D ∧
      (∀ {c : ℝ}, c₀ ≤ c → DifferentiableOn ℂ (W_D c) {w : ℂ | 0 < w.re}) ∧
      (∀ {c x : ℝ}, c₀ ≤ c → 0 < x → (W_D c (x : ℂ)).im = 0) ∧
      (∀ {c x : ℝ}, c₀ ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → 0 ≤ (W_D c (x : ℂ)).re) ∧
      (∀ {c x : ℝ}, c₀ ≤ c → 0 < x → x < x₀ → x ∉ Icc (x₀ / 3) (2 * B₀) →
        b * c ^ (-(1 / 3 : ℝ)) ≤ (W_D c (x : ℂ)).re) ∧
      (∀ {c x : ℝ}, c₀ ≤ c → 2 * B₀ ≤ x → x ≤ c ^ (1 / 3 : ℝ) →
        d_tail * (1 + x) ^ (-(5 / 2 : ℝ)) ≤ (W_D c (x : ℂ)).re) ∧
      (∀ {c x : ℝ}, c₀ ≤ c → x ∈ Icc (x₀ / 3) (2 * B₀) → x ≤ c ^ (1 / 3 : ℝ) →
        c_J * c ^ (-(1 / 3 : ℝ)) ≤ (W_D c (x : ℂ)).re) ∧
      (∀ {c x y : ℝ}, c₀ ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → x ∉ Icc (x₀ / 3) (2 * B₀) → |y| ≤ x / 4 →
        ‖W_D c ((x : ℂ) + (y : ℂ) * Complex.I) - W_D c (x : ℂ)‖ ≤ 4 * M * (|y| / x) * (W_D c (x : ℂ)).re) ∧
      (∀ {c x y : ℝ}, c₀ ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → x ∉ Icc (x₀ / 3) (2 * B₀) →
        ‖W_D c ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Λ * (W_D c (x : ℂ)).re +
          (if x < x₀ ∧ x / 2 < |y| then Λ_add_max * min (|y| ^ (1 / 2 : ℝ)) 1 else 0)) ∧
      (∀ {c : ℝ} {w : ℂ}, c₀ ≤ c → 0 < w.re → ‖W_D c w‖ ≤ K_D) := by
  classical
  intro X Z D W_D
  have hB₀_pos : 0 ≤ B₀ := by linarith
  have hUX : HasU2 X := hasU2_of_genRational hF
  obtain ⟨CX_rhp, hCX_rhp, hX_rhp⟩ := hUX.rhp
  have hUZ : ∀ c : ℝ, HasU2 (Z c) := fun c => hasU2_finset_sum s B b₀₀ b₁₁ hB (fun i => α i c)
  have hUD : ∀ c : ℝ, HasU2 (D c) := fun c => hUX.add ((hUZ c).smul (liftEps c))
  have hZ_split : ∀ (c : ℝ) {w : ℂ}, 0 ≤ w.re →
      airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w) =
        ∑ i ∈ s, (α i c : ℂ) * airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs : ℂ) * w) :=
    fun c {_} hw => airyTwistedLaplaceC_finset_sum s B b₀₀ b₁₁ hB (fun i => α i c) hw
  have hZ_rhp_i : ∀ i ∈ s, ∃ Ci > 0, ∀ w : ℂ, 0 ≤ w.re →
      ‖airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs : ℂ) * w)‖ ≤ Ci * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) :=
    fun i hi => (hasU2_of_genRational (hB i hi)).rhp
  choose CZi hCZi_pos hCZi_bd using hZ_rhp_i
  let CZ_rhp : ℝ := R * (∑ i ∈ s, if hi : i ∈ s then CZi i hi else 0) + 1
  have hCZ_rhp : 0 < CZ_rhp := by
    have : 0 ≤ ∑ i ∈ s, if hi : i ∈ s then CZi i hi else 0 := by
      refine Finset.sum_nonneg fun i hi => ?_
      split_ifs
      exact (hCZi_pos i hi).le
    positivity
  have hZ_rhp : ∀ {c : ℝ} {w : ℂ}, c_min ≤ c → 0 ≤ w.re →
      ‖airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ ≤ CZ_rhp * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
    intro c w hc hw
    rw [hZ_split c hw]
    have hnn : 0 ≤ ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by positivity
    calc ‖∑ i ∈ s, (α i c : ℂ) * airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs : ℂ) * w)‖
        ≤ ∑ i ∈ s, ‖(α i c : ℂ) * airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs : ℂ) * w)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ s, R * ((if hi : i ∈ s then CZi i hi else 0) * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          split_ifs
          exact mul_le_mul (hα i hi c hc) (hCZi_bd i hi w hw) (norm_nonneg _) hR
      _ = (R * ∑ i ∈ s, if hi : i ∈ s then CZi i hi else 0) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
          simp_rw [← mul_assoc, ← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ CZ_rhp * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by dsimp [CZ_rhp]; linarith) hnn
  let Rloc : ℝ := ceCs * (x₀ + 2)
  have hRloc : 0 ≤ Rloc := by have := ceCs_pos; positivity
  obtain ⟨CX_e, hCX_e, hexpX⟩ := u1c_expansion_of_genRational hF Rloc hRloc
  let CX_loc : ℝ := |(β₀₀ + β₁₁) * (2 * ceK * cA)| * Real.sqrt ceCs + CX_e * ceCs * Real.sqrt (x₀ + 2) + 1
  have hCX_loc : 0 < CX_loc := by have := ceCs_pos; positivity
  have hX_loc : ∀ {w : ℂ}, 0 ≤ w.re → ‖w‖ ≤ x₀ + 2 →
      ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ CX_loc * ‖w‖ ^ (1 / 2 : ℝ) := by
    intro w hw hwn
    let y : ℂ := (ceCs : ℂ) * w
    have hyre : 0 ≤ y.re := by simp [y]; exact mul_nonneg ceCs_pos.le hw
    have hyn : ‖y‖ ≤ Rloc := by
      rw [show y = (ceCs : ℂ) * w from rfl, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ceCs_pos]
      exact mul_le_mul_of_nonneg_left hwn ceCs_pos.le
    have h0 : airyTwistedLaplaceC X 0 = 0 := by rw [airyTwistedLaplaceC_zero_eq]; simp [X, hmass]
    have hbd := hexpX hyre hyn
    rw [h0, sub_zero] at hbd
    have hyn_eq : ‖y‖ = ceCs * ‖w‖ := by
      rw [show y = (ceCs : ℂ) * w from rfl, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ceCs_pos]
    have hsqrt_y : ‖y ^ (1 / 2 : ℂ)‖ = Real.sqrt ceCs * ‖w‖ ^ (1 / 2 : ℝ) := by
      rw [norm_cpow_half_eq, hyn_eq, Real.mul_rpow ceCs_pos.le (norm_nonneg w), ← Real.sqrt_eq_rpow]
    have hwn_pow : ‖w‖ ≤ Real.sqrt (x₀ + 2) * ‖w‖ ^ (1 / 2 : ℝ) := by
      calc ‖w‖ = ‖w‖ ^ (1 / 2 : ℝ) * ‖w‖ ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_add_of_nonneg (norm_nonneg w) (by norm_num) (by norm_num)]; norm_num
        _ ≤ Real.sqrt (x₀ + 2) * ‖w‖ ^ (1 / 2 : ℝ) := by
            rw [Real.sqrt_eq_rpow]
            exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg w) hwn (by norm_num)) (by positivity)
    have hterm2 : ‖(((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ =
        |(β₀₀ + β₁₁) * (2 * ceK * cA)| * ‖y ^ (1 / 2 : ℂ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖airyTwistedLaplaceC X y‖
        = ‖(airyTwistedLaplaceC X y + (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)) -
            (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ := by ring_nf
      _ ≤ ‖airyTwistedLaplaceC X y + (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ +
            ‖(((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ := norm_sub_le _ _
      _ ≤ CX_e * ‖y‖ + |(β₀₀ + β₁₁) * (2 * ceK * cA)| * ‖y ^ (1 / 2 : ℂ)‖ := by
          rw [hterm2]; exact add_le_add hbd le_rfl
      _ = CX_e * ceCs * ‖w‖ + |(β₀₀ + β₁₁) * (2 * ceK * cA)| * Real.sqrt ceCs * ‖w‖ ^ (1 / 2 : ℝ) := by
          rw [hyn_eq, hsqrt_y]; ring
      _ ≤ (CX_e * ceCs * Real.sqrt (x₀ + 2) + |(β₀₀ + β₁₁) * (2 * ceK * cA)| * Real.sqrt ceCs) *
            ‖w‖ ^ (1 / 2 : ℝ) := by
          have h1 : CX_e * ceCs * ‖w‖ ≤ CX_e * ceCs * Real.sqrt (x₀ + 2) * ‖w‖ ^ (1 / 2 : ℝ) := by
            calc CX_e * ceCs * ‖w‖ ≤ CX_e * ceCs * (Real.sqrt (x₀ + 2) * ‖w‖ ^ (1 / 2 : ℝ)) :=
                  mul_le_mul_of_nonneg_left hwn_pow (by have := ceCs_pos; positivity)
              _ = _ := by ring
          linarith
      _ ≤ CX_loc * ‖w‖ ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (by dsimp [CX_loc]; linarith) (by positivity)
  have hZ_loc_i : ∀ i ∈ s, ∃ Ci > 0, ∀ x ∈ Icc (0 : ℝ) x₀,
      ‖airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ) -
        airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) 0‖ ≤ Ci * Real.sqrt x := by
    intro i hi
    obtain ⟨Ci_e, hCi_e, hexp_i⟩ := u1c_expansion_of_genRational (hB i hi) Rloc hRloc
    have hCpos : 0 < |(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| * Real.sqrt ceCs + Ci_e * ceCs * Real.sqrt x₀ + 1 := by
      have := ceCs_pos; positivity
    refine ⟨|(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| * Real.sqrt ceCs + Ci_e * ceCs * Real.sqrt x₀ + 1,
      hCpos, fun x ⟨hx0, hxx₀⟩ => ?_⟩
    let y : ℂ := ((ceCs * x : ℝ) : ℂ)
    have hyre : 0 ≤ y.re := by simp [y]; exact mul_nonneg ceCs_pos.le hx0
    have hyn : ‖y‖ ≤ Rloc := by
      rw [show y = ((ceCs * x : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg ceCs_pos.le hx0)]
      exact mul_le_mul_of_nonneg_left (by linarith) ceCs_pos.le
    have hbd := hexp_i hyre hyn
    have hyn_eq : ‖y‖ = ceCs * x := by
      rw [show y = ((ceCs * x : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg ceCs_pos.le hx0)]
    have hsqrt_y : ‖y ^ (1 / 2 : ℂ)‖ = Real.sqrt ceCs * Real.sqrt x := by
      rw [norm_cpow_half_eq, hyn_eq, Real.mul_rpow ceCs_pos.le hx0, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    have hx_pow : x ≤ Real.sqrt x₀ * Real.sqrt x := by
      calc x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0).symm
        _ ≤ Real.sqrt x₀ * Real.sqrt x := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hxx₀) (Real.sqrt_nonneg x)
    have hterm2 : ‖(((b₀₀ i + b₁₁ i) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ =
        |(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| * ‖y ^ (1 / 2 : ℂ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) y -
            airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) 0‖
        = ‖(airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) y -
              airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) 0 +
              (((b₀₀ i + b₁₁ i) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)) -
            (((b₀₀ i + b₁₁ i) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ := by ring_nf
      _ ≤ Ci_e * ‖y‖ + |(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| * ‖y ^ (1 / 2 : ℂ)‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [hterm2]; exact add_le_add hbd le_rfl
      _ = Ci_e * ceCs * x + |(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| * Real.sqrt ceCs * Real.sqrt x := by
          rw [hyn_eq, hsqrt_y]; ring
      _ ≤ (|(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| * Real.sqrt ceCs + Ci_e * ceCs * Real.sqrt x₀ + 1) *
            Real.sqrt x := by
          have h1 : Ci_e * ceCs * x ≤ Ci_e * ceCs * Real.sqrt x₀ * Real.sqrt x := by
            calc Ci_e * ceCs * x ≤ Ci_e * ceCs * (Real.sqrt x₀ * Real.sqrt x) :=
                  mul_le_mul_of_nonneg_left hx_pow (by have := ceCs_pos; positivity)
              _ = _ := by ring
          linarith [Real.sqrt_nonneg x]
  choose CZ_loc_i hCZ_loc_pos hCZ_loc_bd using hZ_loc_i
  let CZ_loc : ℝ := R * (∑ i ∈ s, if hi : i ∈ s then CZ_loc_i i hi else 0) + 1
  have hCZ_loc : 0 < CZ_loc := by
    have : 0 ≤ ∑ i ∈ s, if hi : i ∈ s then CZ_loc_i i hi else 0 := by
      refine Finset.sum_nonneg fun i hi => ?_
      split_ifs
      exact (hCZ_loc_pos i hi).le
    positivity
  have hZ_loc : ∀ c x : ℝ, c_min ≤ c → x ∈ Icc (0 : ℝ) x₀ →
      |airyTwistedLaplace (Z c) (ceCs * x) - airyTwistedLaplace (Z c) 0| ≤ CZ_loc * Real.sqrt x := by
    intro c x hc hx
    have hsplit_x : airyTwistedLaplaceC (Z c) ((ceCs * x : ℝ) : ℂ) =
        ∑ i ∈ s, (α i c : ℂ) * airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ) := by
      have h0 := hZ_split c (w := (x : ℂ)) (by simp; exact hx.1)
      have hcx : (ceCs : ℂ) * (x : ℂ) = ((ceCs * x : ℝ) : ℂ) := by push_cast; ring
      rw [← hcx]; exact h0
    have hsplit_0 : airyTwistedLaplaceC (Z c) 0 =
        ∑ i ∈ s, (α i c : ℂ) * airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) 0 := by
      have h0 := hZ_split c (w := 0) le_rfl
      rwa [mul_zero] at h0
    have hbd_c : ‖airyTwistedLaplaceC (Z c) ((ceCs * x : ℝ) : ℂ) - airyTwistedLaplaceC (Z c) 0‖ ≤
        CZ_loc * Real.sqrt x := by
      rw [hsplit_x, hsplit_0, ← Finset.sum_sub_distrib]
      calc ‖∑ i ∈ s, ((α i c : ℂ) * airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ) -
              (α i c : ℂ) * airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) 0)‖
          ≤ ∑ i ∈ s, ‖(α i c : ℂ) * (airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ) -
              airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) 0)‖ := by
            refine (norm_sum_le _ _).trans (le_of_eq ?_); congr 1; ext i; rw [mul_sub]
        _ ≤ ∑ i ∈ s, R * ((if hi : i ∈ s then CZ_loc_i i hi else 0) * Real.sqrt x) := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            split_ifs
            exact mul_le_mul (hα i hi c hc) (hCZ_loc_bd i hi x hx) (norm_nonneg _) hR
        _ = (R * ∑ i ∈ s, if hi : i ∈ s then CZ_loc_i i hi else 0) * Real.sqrt x := by
            simp_rw [← mul_assoc, ← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ CZ_loc * Real.sqrt x :=
            mul_le_mul_of_nonneg_right (by dsimp [CZ_loc]; linarith) (Real.sqrt_nonneg x)
    rw [airyTwistedLaplaceC_ofReal, show (0 : ℂ) = ((0 : ℝ) : ℂ) from Complex.ofReal_zero.symm,
      airyTwistedLaplaceC_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hbd_c
    exact hbd_c
  let E_max : ℝ := max (2 * CZ_loc / c₁') (2 * CZ_rhp / d₀)
  have hE_max : 0 < E_max := by positivity
  let c₀ : ℝ := max c_min (max ((E_max + 1) ^ 3) ((2 * B₀ + 1) ^ 3))
  have hc₀_min : c_min ≤ c₀ := le_max_left _ _
  have hc₀_2 : 2 ≤ c₀ := hc_min.trans hc₀_min
  have hε_small : ∀ {c : ℝ}, c₀ ≤ c → liftEps c * CZ_loc ≤ c₁' / 2 ∧ liftEps c * CZ_rhp ≤ d₀ / 2 ∧
      2 * B₀ ≤ c ^ (1 / 3 : ℝ) := by
    intro c hc
    have hE3 : (E_max + 1) ^ 3 ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
    have hB3 : (2 * B₀ + 1) ^ 3 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
    have hc0 : 0 < c := by linarith
    have hcube := liftEps_cube_mul hc0
    have hinv : liftEps c ≤ (E_max + 1)⁻¹ := by
      have hpow : liftEps c ^ 3 ≤ ((E_max + 1)⁻¹) ^ 3 := by
        rw [inv_pow]
        have : c⁻¹ ≤ ((E_max + 1) ^ 3)⁻¹ := inv_anti₀ (by positivity) hE3
        have hce : liftEps c ^ 3 = c⁻¹ := by
          calc liftEps c ^ 3 = (liftEps c ^ 3 * c) * c⁻¹ := by field_simp [hc0.ne']
            _ = c⁻¹ := by rw [hcube, one_mul]
        linarith
      by_contra hlt; push Not at hlt
      exact absurd (pow_lt_pow_left₀ hlt (by positivity) (by norm_num : 3 ≠ 0)) (by linarith)
    have h1 : liftEps c * CZ_loc ≤ c₁' / 2 := by
      have hE1 : 2 * CZ_loc / c₁' ≤ E_max := le_max_left _ _
      have h2 : liftEps c * (2 * CZ_loc / c₁') ≤ 1 := by
        calc liftEps c * (2 * CZ_loc / c₁') ≤ (E_max + 1)⁻¹ * E_max :=
              mul_le_mul hinv hE1 (by positivity) (by positivity)
          _ ≤ 1 := by rw [inv_mul_le_one₀ (by positivity)]; linarith
      have : liftEps c * CZ_loc = (c₁' / 2) * (liftEps c * (2 * CZ_loc / c₁')) := by
        field_simp [hc₁'.ne']
      rw [this]; nlinarith [hc₁']
    have h2 : liftEps c * CZ_rhp ≤ d₀ / 2 := by
      have hE2 : 2 * CZ_rhp / d₀ ≤ E_max := le_max_right _ _
      have h2' : liftEps c * (2 * CZ_rhp / d₀) ≤ 1 := by
        calc liftEps c * (2 * CZ_rhp / d₀) ≤ (E_max + 1)⁻¹ * E_max :=
              mul_le_mul hinv hE2 (by positivity) (by positivity)
          _ ≤ 1 := by rw [inv_mul_le_one₀ (by positivity)]; linarith
      have : liftEps c * CZ_rhp = (d₀ / 2) * (liftEps c * (2 * CZ_rhp / d₀)) := by
        field_simp [hd₀.ne']
      rw [this]; nlinarith [hd₀]
    have h3 : 2 * B₀ ≤ c ^ (1 / 3 : ℝ) := by
      have hp3 : (c ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = c := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
      have hBpos : 0 ≤ 2 * B₀ := by linarith
      have hpow : (2 * B₀) ^ 3 ≤ (c ^ (1 / 3 : ℝ)) ^ 3 := by
        rw [hp3]
        calc (2 * B₀) ^ 3 ≤ (2 * B₀ + 1) ^ 3 := pow_le_pow_left₀ hBpos (by linarith) 3
          _ ≤ c := hB3
      by_contra hlt; push Not at hlt
      exact absurd (pow_lt_pow_left₀ hlt (Real.rpow_nonneg hc0.le _) (by norm_num : 3 ≠ 0)) (by linarith)
    exact ⟨h1, h2, h3⟩
  let a_cap : ℝ := ceCs * ceBeta1 * K / (2 * (m : ℝ))
  have ha_cap : 0 < a_cap := by have := ceCs_pos; have := ceBeta1_pos; positivity
  let k_mult : ℝ := (1 + a_cap)⁻¹ ^ m
  have hk_mult : 0 < k_mult := by positivity
  have hmult_floor : ∀ {c x : ℝ}, c₀ ≤ c → 0 ≤ x → x ≤ c ^ (1 / 3 : ℝ) →
      k_mult ≤ uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m := by
    intro c x hc hx hx_top
    have hc0 : 0 < c := by linarith
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hε_c : liftEps c * c ^ (1 / 3 : ℝ) = 1 := by
      have hpow : (liftEps c * c ^ (1 / 3 : ℝ)) ^ 3 = 1 := by
        have hp3 : (c ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = c := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
        calc (liftEps c * c ^ (1 / 3 : ℝ)) ^ 3 = liftEps c ^ 3 * (c ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by ring
          _ = liftEps c ^ 3 * c := by rw [hp3]
          _ = 1 := liftEps_cube_mul hc0
      have hn : 0 ≤ liftEps c * c ^ (1 / 3 : ℝ) := mul_nonneg (liftEps_pos hc0).le (Real.rpow_nonneg hc0.le _)
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact absurd (pow_lt_pow_left₀ hlt hn (by norm_num : 3 ≠ 0)) (by linarith)
      · exact absurd (pow_lt_pow_left₀ hgt zero_le_one (by norm_num : 3 ≠ 0)) (by linarith)
    have hx_le : liftEps c * x ≤ 1 := by
      calc liftEps c * x ≤ liftEps c * c ^ (1 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_left hx_top (liftEps_pos hc0).le
        _ = 1 := hε_c
    have hprod_le : ceCs * (ceBeta1 * K * liftEps c / 2) / m * x ≤ a_cap := by
      calc ceCs * (ceBeta1 * K * liftEps c / 2) / m * x = a_cap * (liftEps c * x) := by
            dsimp [a_cap]; field_simp [hm0]
        _ ≤ a_cap * 1 := mul_le_mul_of_nonneg_left hx_le ha_cap.le
        _ = a_cap := mul_one _
    have hnn : 0 ≤ ceCs * (ceBeta1 * K * liftEps c / 2) / m * x := by
      have := ceCs_pos; have := ceBeta1_pos; have := liftEps_pos hc0; positivity
    exact pow_le_pow_left₀ (by positivity) ((inv_anti₀ (by positivity) (by linarith)).trans (e1r_lower hnn)) m
  have hWD_real : ∀ {c x : ℝ}, 0 ≤ x →
      W_D c (x : ℂ) = (((uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m *
          (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) : ℝ) : ℂ) := by
    intro c x hx
    dsimp [W_D]
    have hD_split : airyTwistedLaplaceC (D c) ((ceCs : ℂ) * (x : ℂ)) =
        airyTwistedLaplaceC X ((ceCs : ℂ) * (x : ℂ)) +
          (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * (x : ℂ)) := by
      have hre : 0 ≤ ((ceCs : ℂ) * (x : ℂ)).re := by simp; exact mul_nonneg ceCs_pos.le hx
      have : D c = fun u => X u + liftEps c * Z c u := rfl
      rw [this, airyTwistedLaplaceC_add (hUX.integrable _ hre) (((hUZ c).smul _).integrable _ hre),
        airyTwistedLaplaceC_const_mul]
    unfold liftSymbol liftMultiplier
    rw [hD_split]
    have h1 : (((ceCs * (ceBeta1 * K * liftEps c / 2) / (m : ℝ) : ℝ) : ℂ) * (x : ℂ)) =
        ((ceCs * (ceBeta1 * K * liftEps c / 2) / m * x : ℝ) : ℂ) := by push_cast; ring
    have h2 : ((ceCs : ℂ) * (x : ℂ)) = ((ceCs * x : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, uctE1r_cast, airyTwistedLaplaceC_ofReal, airyTwistedLaplaceC_ofReal]
    push_cast; ring
  have hWD_re : ∀ {c x : ℝ}, 0 ≤ x → (W_D c (x : ℂ)).re =
      uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m *
        (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) := fun {c x} hx => by
    rw [hWD_real hx, Complex.ofReal_re]
  have hWD_im : ∀ {c x : ℝ}, 0 ≤ x → (W_D c (x : ℂ)).im = 0 := fun {c x} hx => by
    rw [hWD_real hx, Complex.ofReal_im]
  have hX_small_r : ∀ x ∈ Icc (0 : ℝ) x₀, c₁' * Real.sqrt x ≤ airyTwistedLaplace X (ceCs * x) := by
    intro x hx
    have h := hX_small x hx
    rwa [airyTwistedLaplaceC_ofReal, Complex.ofReal_re] at h
  have hX_tail_r : ∀ x : ℝ, B₀ / 2 ≤ x → d₀ * (1 + x) ^ (-(5 / 2 : ℝ)) ≤ airyTwistedLaplace X (ceCs * x) := by
    intro x hx
    have h := hX_tail x hx
    rwa [airyTwistedLaplaceC_ofReal, Complex.ofReal_re] at h
  have hZ0_r : ∀ c : ℝ, c_min ≤ c → ceK * m_Z ≤ airyTwistedLaplace (Z c) 0 := by
    intro c hc
    have heq := airyTwistedLaplaceC_zero_eq (Z c)
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from Complex.ofReal_zero.symm, airyTwistedLaplaceC_ofReal] at heq
    have hre := Complex.ofReal_injective heq
    rw [hre]; exact mul_le_mul_of_nonneg_left (hZ_mass c hc) ceK_pos.le
  have hZ_r : ∀ c x : ℝ, c_min ≤ c → 0 ≤ x →
      |airyTwistedLaplace (Z c) (ceCs * x)| ≤ CZ_rhp * (1 + x) ^ (-(5 / 2 : ℝ)) := by
    intro c x hc hx0
    have h1 := hZ_rhp hc (w := (x : ℂ)) (by simpa using hx0)
    rw [show ((ceCs : ℂ) * (x : ℂ)) = ((ceCs * x : ℝ) : ℂ) by push_cast; ring,
      airyTwistedLaplaceC_ofReal, Complex.norm_real, Real.norm_eq_abs,
      show (1 : ℂ) + (x : ℂ) = ((1 + x : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs] at h1
    have h1p : |1 + x| = 1 + x := abs_of_nonneg (by linarith)
    rw [h1p] at h1
    exact h1
  have hD_small : ∀ {c x : ℝ}, c₀ ≤ c → x ∈ Icc (0 : ℝ) x₀ →
      (c₁' / 2) * Real.sqrt x + ceK * m_Z * liftEps c ≤
        airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x) := by
    intro c x hc hx
    exact ceDualLine_hsmall_bound c₁' m_Z CZ_loc c_min hX_small_r Z hZ0_r hZ_loc
      (hc₀_min.trans hc) (by linarith) hx (hε_small hc).1
  have hD_tail : ∀ {c x : ℝ}, c₀ ≤ c → B₀ / 2 ≤ x →
      (d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ)) ≤
        airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x) := by
    intro c x hc hx
    exact ceDualLine_htail_bound d₀ B₀ CZ_rhp c_min hX_tail_r Z hZ_r
      (hc₀_min.trans hc) (by linarith) hx (by linarith) (hε_small hc).2.1
  have hD_J : ∀ {c x : ℝ}, c₀ ≤ c → x ∈ Icc (x₀ / 3) (2 * B₀) →
      z₀ * liftEps c ≤ airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x) := by
    intro c x hc hx
    have h0 : 0 < c := by linarith
    have hX : 0 ≤ airyTwistedLaplace X (ceCs * x) := by
      rw [airyTwistedLaplace_eq_ceK_airyLaplace]
      exact mul_nonneg ceK_pos.le (hnonneg (ceCs * x) (mul_pos ceCs_pos (by linarith [hx.1])))
    have hZ := hZ_J c (hc₀_min.trans hc) x hx
    rw [airyTwistedLaplaceC_ofReal, Complex.ofReal_re] at hZ
    have hmul : liftEps c * z₀ ≤ liftEps c * airyTwistedLaplace (Z c) (ceCs * x) :=
      mul_le_mul_of_nonneg_left hZ (liftEps_pos h0).le
    linarith
  let b : ℝ := k_mult * (ceK * m_Z)
  let c_J : ℝ := k_mult * z₀
  let d_tail : ℝ := k_mult * (d₀ / 2)
  let M_small : ℝ := (2 : ℝ) ^ m * max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z))
  let M_tail : ℝ := (2 : ℝ) ^ m * (2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2))
  let M : ℝ := max 1 (max M_small M_tail)
  let Λ_add_max : ℝ := max (CX_loc * Real.sqrt 3) CX_rhp
  let K_D : ℝ := CX_rhp + CZ_rhp
  refine ⟨c₀, M, M, Λ_add_max, b, c_J, d_tail, K_D, hc₀_min, le_max_left _ _, le_max_left _ _,
    by positivity, by have := ceK_pos; positivity, by positivity, by positivity, by positivity,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c _; exact liftSymbol_differentiableOn (hUD c) _ m
  · intro c x _ hx; exact hWD_im hx.le
  · intro c x hc hx hx_top
    rw [hWD_re hx.le]
    refine mul_nonneg (pow_nonneg (uctE1r_pos _).le m) ?_
    rcases le_or_gt x (x₀ / 3) with h1 | h1
    · have hDs := hD_small hc ⟨hx.le, by linarith⟩
      have h0 : 0 < c := by linarith
      have hnn1 : 0 ≤ (c₁' / 2) * Real.sqrt x := by positivity
      have hnn2 : 0 ≤ ceK * m_Z * liftEps c := by have := ceK_pos; have := liftEps_pos h0; positivity
      linarith
    · rcases le_or_gt x (2 * B₀) with h2 | h2
      · have hDJ := hD_J hc ⟨h1.le, h2⟩
        have h0 : 0 < c := by linarith
        have hnn : 0 ≤ z₀ * liftEps c := mul_nonneg hz₀.le (liftEps_pos h0).le
        exact hnn.trans hDJ
      · have hDt := hD_tail (x := x) hc (by linarith [hB₀_pos])
        have : 0 ≤ (d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ)) := by positivity
        linarith
  · intro c x hc hx hx_lt _
    rw [hWD_re hx.le]
    have hc0 : 0 < c := by linarith
    have hx_le_c : x ≤ c ^ (1 / 3 : ℝ) := by linarith [(hε_small hc).2.2]
    have hmult := hmult_floor hc hx.le hx_le_c
    have hDs := hD_small hc ⟨hx.le, hx_lt.le⟩
    have hle1 : ceK * m_Z * liftEps c ≤
        airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x) := by
      have : 0 ≤ (c₁' / 2) * Real.sqrt x := by positivity
      linarith
    have hb_eq : b * c ^ (-(1 / 3 : ℝ)) = k_mult * (ceK * m_Z * liftEps c) := by
      unfold liftEps; dsimp [b]; ring
    rw [hb_eq]
    exact mul_le_mul hmult hle1 (by have := ceK_pos; have := liftEps_pos hc0; positivity)
      (pow_nonneg (uctE1r_pos _).le _)
  · intro c x hc hxB hx_top
    rw [hWD_re (by linarith)]
    have hmult := hmult_floor hc (by linarith) hx_top
    have hDt := hD_tail (x := x) hc (by linarith [hB₀_pos])
    dsimp [d_tail]
    calc k_mult * (d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ))
        = k_mult * ((d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ))) := by ring
      _ ≤ _ := mul_le_mul hmult hDt (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith [hB₀_pos]) _))
          (pow_nonneg (uctE1r_pos _).le _)
  · intro c x hc hxJ hx_top
    rw [hWD_re (by linarith [hxJ.1])]
    have hc0 : 0 < c := by linarith
    have hmult := hmult_floor hc (by linarith [hxJ.1]) hx_top
    have hDJ := hD_J hc hxJ
    have hcj_eq : c_J * c ^ (-(1 / 3 : ℝ)) = k_mult * (z₀ * liftEps c) := by
      unfold liftEps; dsimp [c_J]; ring
    rw [hcj_eq]
    exact mul_le_mul hmult hDJ (by have := liftEps_pos hc0; positivity) (pow_nonneg (uctE1r_pos _).le _)
  · intro c x y hc hx _ hx_not hy
    exact ceDualLine_hA1_aux (fun c u => rfl) hUX hUZ hUD hx₀ hB₀_pos hc₁' hd₀ hCX_loc hCX_rhp.le
      hCZ_rhp hm_Z hc₀_2 rfl rfl ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _)) hX_loc hX_rhp
      (fun hc' => hZ_rhp (hc₀_min.trans hc')) hD_small hD_tail hWD_re (by linarith) hm hc hx hx_not hy
  · intro c x y hc hx _ hx_not
    exact ceDualLine_hA2_aux (fun c u => rfl) hUX hUZ hx₀ hx₀B hB₀_pos hc₁' hd₀ hCX_loc hCX_rhp.le
      hCZ_rhp hm_Z hc₀_2 ((le_max_left _ _).trans (le_max_right _ _)) rfl
      ((le_max_right _ _).trans (le_max_right _ _)) (le_max_left _ _) (le_max_right _ _)
      hX_loc hX_rhp (fun hc' => hZ_rhp (hc₀_min.trans hc')) hD_small hD_tail hWD_re (by linarith)
      hc hx hx_not
  · intro c w hc hw
    have hc0 : 0 < c := by linarith
    have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by
      have := ceBeta1_pos; have := liftEps_pos hc0; positivity
    have h1w : 1 ≤ ‖1 + w‖ := by
      have := Complex.re_le_norm (1 + w)
      simp only [Complex.add_re, Complex.one_re] at this; linarith
    have hpow1 : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h1w (by norm_num)
    have hXw := (hX_rhp w hw.le).trans (mul_le_of_le_one_right hCX_rhp.le hpow1)
    have hZw := (hZ_rhp (hc₀_min.trans hc) hw.le).trans (mul_le_of_le_one_right hCZ_rhp.le hpow1)
    have hε1 : liftEps c ≤ 1 := liftEps_le_one_of_two_le (hc₀_2.trans hc)
    have hD_split : airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w) =
        airyTwistedLaplaceC X ((ceCs : ℂ) * w) +
          (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w) := by
      have hre : 0 ≤ ((ceCs : ℂ) * w).re := by simp; exact mul_nonneg ceCs_pos.le hw.le
      have : D c = fun u => X u + liftEps c * Z c u := rfl
      rw [this, airyTwistedLaplaceC_add (hUX.integrable _ hre) (((hUZ c).smul _).integrable _ hre),
        airyTwistedLaplaceC_const_mul]
    dsimp [W_D, liftSymbol]
    rw [norm_mul, hD_split]
    calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ *
          ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w) + (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖
        ≤ 1 * (CX_rhp + 1 * CZ_rhp) := by
          refine mul_le_mul (norm_liftMultiplier_le_one hδ0 m hw.le) ?_ (norm_nonneg _) zero_le_one
          calc ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w) + (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖
              ≤ ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ +
                  ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ := norm_add_le _ _
            _ ≤ CX_rhp + 1 * CZ_rhp := by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (liftEps_pos hc0)]
                exact add_le_add hXw (mul_le_mul hε1 hZw (norm_nonneg _) zero_le_one)
      _ = CX_rhp + CZ_rhp := by ring

/-- info: 'FormalResearch.SignUncertainty.ce_dual_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_dual_line

end FormalResearch.SignUncertainty
