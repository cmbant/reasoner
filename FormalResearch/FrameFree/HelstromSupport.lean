import FormalResearch.FrameFree.Helstrom
import FormalResearch.FrameFree.Ceilings

/-!
# The support test (Paper P, `thm:supportrate`, error half) and calibration

Namespace `FormalResearch.FrameFree.Helstrom`.  With `W_k = span{(gΘψ)^{⊗k} : g ∈ SL(2,ℂ)^n}` (the span of the
filter orbit of `Θψ`; its Zariski closure has the same span) and `R_k = ‖Π_{W_k} ψ^{⊗k}‖²`:

* `suppSpace_invariant`: `W_k` is `K`-invariant, so `Π_{W_k}` is a `K`-invariant test (`suppEffect_isInv`);
* `Pe_le_half_Rk`: `P_e(k) ≤ R_k/2` (the support test never errs on `Θψ`);
* `normalised_pow_le_Rk`, `FCΘ_pow_le_Rk`: `R_k ≥ (|⟨ψ|gΘψ⟩|²/‖gΘψ‖²)^k`, hence `R_k ≥ F_C(ψ)^k` (the
  elementary half of `thm:supportrate`).

**The hard half of `thm:supportrate`.**  The upper half `limsup R_k^{1/k} ≤ F_C`
(`SupportRateUpper`) is proved in `PolyImageDischarge` (`SupportRate.polyImageClosure`: density of a polynomial
image in its Zariski closure); here it is a hypothesis of the lemmas below, which the unconditional
versions in `PolyImageDischarge` and `XiInvUnconditional` specialise gives `xi_ge_of_support` (`ξ_inv ≥ -log F_C`) and, with `F_C = F_K`, `tendsto_of_calibrated`
(`-(1/k) log P_e(k) → C_K`: `cor:calibrated`).
-/

open scoped ComplexConjugate Matrix BigOperators InnerProductSpace ComplexOrder
open Matrix FormalResearch.FrameFree.NQubit

set_option linter.unusedSectionVars false

namespace FormalResearch.FrameFree.Helstrom

theorem kron_conjTranspose {I α : Type*} [Fintype I] (M : I → Matrix α α ℂ) :
    (kron M)ᴴ = kron (fun i => (M i)ᴴ) := by
  ext x y
  simp [kron, Matrix.conjTranspose_apply, star_prod]

theorem rotK_conjTranspose {n : ℕ} (k : ℕ) (u : Fin n → Op1) :
    (rotK k u)ᴴ = rotK k (fun i => (u i)ᴴ) := by
  unfold rotK
  rw [kron_conjTranspose]
  congr 1
  funext j
  exact kron_conjTranspose u

/-- The span of the `k`-th tensor powers of the filter orbit of `Θψ`. -/
def suppSpace {n : ℕ} (k : ℕ) (ψ : Ψ n) : Submodule ℂ (EuclideanSpace ℂ (Copies n k)) :=
  Submodule.span ℂ {w | ∃ g : Fin n → Op1, (∀ i, (g i).det = 1) ∧
    w = WithLp.toLp 2 (copies k (rot g (Θ ψ)))}

/-- The support error `R_k = ‖Π_{W_k} ψ^{⊗k}‖²`. -/
noncomputable def Rk {n : ℕ} (k : ℕ) (ψ : Ψ n) : ℝ :=
  ‖(suppSpace k ψ).starProjection (WithLp.toLp 2 (copies k ψ))‖ ^ 2

/-- The support test as a matrix. -/
noncomputable def suppEffect {n : ℕ} (k : ℕ) (ψ : Ψ n) : Matrix (Copies n k) (Copies n k) ℂ :=
  projMat (suppSpace k ψ)

theorem copies_mem_suppSpace {n : ℕ} (k : ℕ) (ψ : Ψ n) (g : Fin n → Op1) (hg : ∀ i, (g i).det = 1) :
    WithLp.toLp 2 (copies k (rot g (Θ ψ))) ∈ suppSpace k ψ :=
  Submodule.subset_span ⟨g, hg, rfl⟩

/-- `W_k` is invariant under `rotK k u` for `u ∈ SU(2)^n`. -/
theorem suppSpace_invariant {n : ℕ} (k : ℕ) (ψ : Ψ n) (u : Fin n → Op1) (hu : ∀ i, SU2 (u i)) :
    ∀ v : Copies n k → ℂ, WithLp.toLp 2 v ∈ suppSpace k ψ →
      WithLp.toLp 2 (rotK k u *ᵥ v) ∈ suppSpace k ψ := by
  have key : ∀ x ∈ suppSpace k ψ, WithLp.toLp 2 (rotK k u *ᵥ WithLp.ofLp x) ∈ suppSpace k ψ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      have h : rotK k u *ᵥ copies k (rot g (Θ ψ)) = copies k (rot (fun i => u i * g i) (Θ ψ)) := by
        rw [← rot_comp, copies_rot k u (rot g (Θ ψ))]
      rw [WithLp.ofLp_toLp, h]
      exact copies_mem_suppSpace k ψ _ fun i => by rw [Matrix.det_mul, (hu i).2, hg i, one_mul]
    | zero => simp
    | add x y _ _ hx hy =>
      have := Submodule.add_mem _ hx hy
      simpa [Matrix.mulVec_add] using this
    | smul a x _ hx =>
      have := Submodule.smul_mem _ a hx
      simpa [Matrix.mulVec_smul] using this
  intro v hv
  simpa using key _ hv

theorem suppEffect_isInv {n : ℕ} (k : ℕ) (ψ : Ψ n) : IsInvEffect (n := n) k (suppEffect k ψ) := by
  refine ⟨projMat_isEffect _, fun u hu => ?_⟩
  refine projMat_commute _ (fun v hv => ?_) (fun v hv => ?_)
  · exact suppSpace_invariant k ψ u hu v hv
  · rw [rotK_conjTranspose]
    exact suppSpace_invariant k ψ _ (fun i => SU2_adjoint (hu i)) v hv

/-- **The support test** (`thm:supportrate`, error half): `P_e(k) ≤ R_k / 2`. -/
theorem Pe_le_half_Rk {n : ℕ} (k : ℕ) (ψ : Ψ n) : Pe k ψ ≤ Rk k ψ / 2 := by
  have hbdd : BddBelow {r | ∃ E, IsInvEffect (n := n) k E ∧ r = err E (copies k ψ) (copies k (Θ ψ))} :=
    ⟨0, by rintro r ⟨E, hE, rfl⟩; exact err_nonneg hE.1 _ _⟩
  refine (csInf_le hbdd ⟨suppEffect k ψ, suppEffect_isInv k ψ, rfl⟩).trans (le_of_eq ?_)
  have hb : WithLp.toLp 2 (copies k (Θ ψ)) ∈ suppSpace k ψ := by
    have := copies_mem_suppSpace k ψ (fun _ => 1) (fun i => by simp)
    simpa [rot_one] using this
  unfold err suppEffect Rk
  rw [qf_one_sub_projMat_of_mem _ hb, qf_projMat_self]
  simp

theorem inner_toLp {ι : Type*} [Fintype ι] (v w : ι → ℂ) :
    ⟪WithLp.toLp 2 v, WithLp.toLp 2 w⟫_ℂ = star v ⬝ᵥ w := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- `R_k ≥ (|⟨ψ|gΘψ⟩|²/‖gΘψ‖²)^k` for every filter `g`. -/
theorem normalised_pow_le_Rk {n : ℕ} (k : ℕ) (ψ : Ψ n) (g : Fin n → Op1) (hg : ∀ i, (g i).det = 1)
    (hne : nsq (rot g (Θ ψ)) ≠ 0) :
    (Complex.normSq (ip ψ (rot g (Θ ψ))) / nsq (rot g (Θ ψ))) ^ k ≤ Rk k ψ := by
  set φ := rot g (Θ ψ) with hφ
  set z : EuclideanSpace ℂ (Copies n k) := WithLp.toLp 2 (copies k φ) with hz
  set a : EuclideanSpace ℂ (Copies n k) := WithLp.toLp 2 (copies k ψ) with ha
  have hzW : z ∈ suppSpace k ψ := copies_mem_suppSpace k ψ g hg
  have h0 := Submodule.starProjection_inner_eq_zero a z hzW
  have h1 : ⟪a, z⟫_ℂ = ⟪(suppSpace k ψ).starProjection a, z⟫_ℂ := by
    have := inner_sub_left a ((suppSpace k ψ).starProjection a) z (𝕜 := ℂ)
    rw [h0] at this
    exact (sub_eq_zero.1 this.symm)
  have hcs := norm_inner_le_norm (𝕜 := ℂ) ((suppSpace k ψ).starProjection a) z
  rw [← h1] at hcs
  have hlhs : ‖⟪a, z⟫_ℂ‖ ^ 2 = Complex.normSq (ip ψ φ) ^ k := by
    rw [ha, hz, inner_toLp, star_copies_dot, ← ip_eq_dot, norm_pow, ← pow_mul, mul_comm, pow_mul,
      Complex.normSq_eq_norm_sq]
  have hz2 : ‖z‖ ^ 2 = nsq φ ^ k := by
    have h2 : ⟪z, z⟫_ℂ = ((nsq φ ^ k : ℝ) : ℂ) := by
      rw [hz, inner_toLp, star_copies_dot, ← ip_eq_dot, ip_self]; push_cast; rfl
    rw [inner_self_eq_norm_sq_to_K] at h2
    have h3 : ((‖z‖ ^ 2 : ℝ) : ℂ) = ((nsq φ ^ k : ℝ) : ℂ) := by push_cast at h2 ⊢; exact h2
    exact_mod_cast h3
  have hpos : 0 < nsq φ := lt_of_le_of_ne (Ceilings.nsq_nonneg' φ) (Ne.symm hne)
  have hsq : ‖⟪a, z⟫_ℂ‖ ^ 2 ≤ (‖(suppSpace k ψ).starProjection a‖ * ‖z‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hcs 2
  rw [mul_pow, hlhs, hz2] at hsq
  rw [div_pow, div_le_iff₀ (by positivity)]
  unfold Rk
  linarith

/-- **`R_k ≥ F_C(ψ)^k`** (the elementary half of `thm:supportrate`). -/
theorem FCΘ_pow_le_Rk {n : ℕ} (ψ : Ψ n) {k : ℕ} (hk : k ≠ 0) :
    Ceilings.FCΘ ψ ^ k ≤ Rk k ψ := by
  have hR : 0 ≤ Rk k ψ := by unfold Rk; positivity
  set B := Rk k ψ ^ ((k : ℝ)⁻¹) with hB
  have hBk : B ^ k = Rk k ψ := Real.rpow_inv_natCast_pow hR hk
  have hB0 : 0 ≤ B := Real.rpow_nonneg hR _
  have h1 : Ceilings.FCΘ ψ ≤ B := by
    unfold Ceilings.FCΘ Ceilings.FC
    refine Real.sSup_le ?_ hB0
    rintro r ⟨g, hg, hne, rfl⟩
    have h := normalised_pow_le_Rk k ψ g hg hne
    refine le_of_pow_le_pow_left₀ hk hB0 ?_
    rw [hBk]; exact h
  calc Ceilings.FCΘ ψ ^ k ≤ B ^ k := pow_le_pow_left₀ (Ceilings.FCΘ_nonneg ψ) h1 k
    _ = Rk k ψ := hBk

/-- The upper half of `thm:supportrate` (`limsup R_k^{1/k} ≤ F_C`).  A hypothesis here; proved for every `ψ`
as `SupportRate.supportRateUpper` (`PolyImageDischarge`), by a spectral-radius argument for compressed
multiplication operators on the graded symmetric-power space. -/
def SupportRateUpper {n : ℕ} (ψ : Ψ n) : Prop :=
  ∀ c : ℝ, Ceilings.FCΘ ψ < c → ∀ᶠ k : ℕ in Filter.atTop, Rk k ψ ≤ c ^ k

/-- **`ξ_inv ≥ -log F_C`** (`thm:supportrate`, second sentence), given the upper half of the support rate:
for every `c > F_C(ψ)`, eventually `-(1/k) log P_e(k) ≥ -log c`. -/
theorem eventually_neg_log_c_le {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) (hsr : SupportRateUpper ψ)
    {c : ℝ} (hc : Ceilings.FCΘ ψ < c) :
    ∀ᶠ k : ℕ in Filter.atTop, -Real.log c ≤ -(1 / (k : ℝ)) * Real.log (Pe k ψ) := by
  have hc0 : 0 < c := lt_of_le_of_lt (Ceilings.FCΘ_nonneg ψ) hc
  filter_upwards [hsr c hc, Filter.eventually_ge_atTop 1] with k hk hk1
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hPe := Pe_le_half_Rk k ψ
  have hpos := Pe_pos ψ hψ k
  have h1 : Pe k ψ ≤ c ^ k / 2 := by linarith
  have h2 := Real.log_le_log hpos h1
  rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : -(1 / (k : ℝ)) * (k * Real.log c - Real.log 2) ≤ -(1 / (k : ℝ)) * Real.log (Pe k ψ) :=
    mul_le_mul_of_nonpos_left h2 (by have : 0 < 1 / (k : ℝ) := by positivity
                                     linarith)
  have e : -(1 / (k : ℝ)) * (k * Real.log c - Real.log 2) = -Real.log c + Real.log 2 / k := by
    field_simp
    ring
  have : 0 ≤ Real.log 2 / k := by positivity
  linarith

/-- **`cor:calibrated`** (given the upper half of `thm:supportrate`): if `F_C(ψ) = F_K(ψ)` then
`-(1/k) log P_e(k) → C_K(ψ)`, i.e. `ξ_inv(ψ) = C_K(ψ)`. -/
theorem tendsto_of_calibrated {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) (hsr : SupportRateUpper ψ)
    (hcal : Ceilings.FCΘ ψ = FKΘ ψ) :
    Filter.Tendsto (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (Pe k ψ)) Filter.atTop (nhds (CK ψ)) := by
  have hpos := FKΘ_pos ψ hψ
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- lower side
    set δ := (CK ψ - a) / 2 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    set c := FKΘ ψ * Real.exp δ with hc
    have hc1 : Ceilings.FCΘ ψ < c := by
      rw [hcal, hc]
      have : 1 < Real.exp δ := by simpa using Real.exp_lt_exp.2 hδpos
      nlinarith
    have hlog : -Real.log c = CK ψ - δ := by
      rw [hc, Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]
      unfold CK; ring
    filter_upwards [eventually_neg_log_c_le ψ hψ hsr hc1] with k hk
    linarith
  · -- upper side
    have hmid : CK ψ < (CK ψ + b) / 2 := by linarith
    filter_upwards [eventually_neg_log_Pe_le ψ hψ hmid] with k hk
    linarith

end FormalResearch.FrameFree.Helstrom
