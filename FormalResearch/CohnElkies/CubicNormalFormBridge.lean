module

public import FormalResearch.CohnElkies.CubicNormalFormContraction
public import FormalResearch.CohnElkies.ComplexEdgePhase
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Lemma `O.4(2)`: from the fixed point to the normal-form map `τ(θ)` (`u1co:O4`)

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of Lemma O.4(2).

For `L ∈ (0, 0.002]` put `α̃ = edgeAlphaTilde L`, `θ₀² = 12 α̃ / π²`, `σ₀ = τ₀ / θ₀`
(`τ₀ = tau0 L`), `Φ_mod(θ) = α̃ θ - π² θ³ / 36` and `Φ̂(θ) = Φ_L(σ₀ θ)` for the holomorphic edge phase
`Φ_L = edgePhiC L` (`ComplexEdgePhase`). The quotient
`F(θ) = (Φ̂(θ) - Φ_mod(θ)) / (θ (θ² - θ₀²)²)` is the paper's `𝓕`.

**Named hypothesis** `O4QuotientBound L` (the paper's `M_F ≤ 0.13`, `[O4C (B)]`, interval arithmetic in
`certify_u1c_o4_contraction.py`): `‖F‖ ≤ 0.13` on `D(0, 0.25)` off its three removable singularities.
Everything below is unconditional given that hypothesis: the removable singularities are filled by
Riemann's theorem (the bound supplies boundedness), `o4_fixed_point` gives `η`, and
`τ(θ) = σ₀ θ (1 + (θ² - θ₀²) η(θ))` solves `Φ_L(τ(θ)) = Φ_mod(θ)` on `D(0, 0.22)`.
-/

@[expose] public section

open Metric Set Filter Topology Complex Function
open scoped Real

namespace FormalResearch.CohnElkies

/-! ### Riemann's removable singularity theorem at finitely many points, with a bound -/

/-- Filling finitely many removable singularities of a bounded holomorphic function on an open set,
keeping the bound. -/
theorem removable_finite {U : Set ℂ} (hU : IsOpen U) (B : ℝ) (pts : Finset ℂ) :
    ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (U \ pts) → (∀ z ∈ U \ pts, ‖f z‖ ≤ B) →
      ∃ F : ℂ → ℂ, DifferentiableOn ℂ F U ∧ (∀ z ∈ U \ pts, F z = f z) ∧ ∀ z ∈ U, ‖F z‖ ≤ B := by
  classical
  induction pts using Finset.induction_on with
  | empty =>
      intro f hd hb
      exact ⟨f, by simpa using hd, fun z _ => rfl, fun z hz => hb z (by simpa using hz)⟩
  | insert a s ha ih =>
      intro f hd hb
      have hUs : IsOpen (U \ (s : Set ℂ)) := hU.sdiff s.finite_toSet.isClosed
      by_cases haU : a ∈ U \ (s : Set ℂ)
      · set f1 : ℂ → ℂ := update f a (limUnder (𝓝[≠] a) f) with hf1
        have hset : (U \ (s : Set ℂ)) \ {a} = U \ ((insert a s : Finset ℂ) : Set ℂ) := by
          ext z; simp only [Set.mem_sdiff, mem_singleton_iff, Finset.coe_insert, mem_insert_iff, not_or]; tauto
        have hd1 : DifferentiableOn ℂ f1 (U \ (s : Set ℂ)) := by
          refine Complex.differentiableOn_update_limUnder_of_bddAbove (hUs.mem_nhds haU) (hset ▸ hd) ?_
          refine ⟨B, ?_⟩
          rintro _ ⟨z, hz, rfl⟩
          exact hb z (hset ▸ hz)
        have hf1eq : ∀ z ∈ U \ ((insert a s : Finset ℂ) : Set ℂ), f1 z = f z := fun z hz => by
          have hza : z ≠ a := by
            intro h; apply hz.2; rw [h]; simp
          simp [hf1, hza]
        have hbnd : ∀ z ∈ U \ (s : Set ℂ), ‖f1 z‖ ≤ B := by
          intro z hz
          by_cases hza : z = a
          · subst hza
            have hcont : ContinuousAt f1 z := (hd1.differentiableAt (hUs.mem_nhds hz)).continuousAt
            have ht : Tendsto (fun w => ‖f1 w‖) (𝓝[≠] z) (𝓝 ‖f1 z‖) :=
              (hcont.norm.tendsto).mono_left nhdsWithin_le_nhds
            refine le_of_tendsto ht ?_
            have hnb : (U \ (s : Set ℂ)) ∈ 𝓝[≠] z := mem_nhdsWithin_of_mem_nhds (hUs.mem_nhds hz)
            filter_upwards [hnb, self_mem_nhdsWithin] with w hw hwz
            have hw' : w ∈ U \ ((insert z s : Finset ℂ) : Set ℂ) := by
              refine ⟨hw.1, ?_⟩
              simp only [Finset.coe_insert, mem_insert_iff, not_or]
              exact ⟨hwz, hw.2⟩
            rw [hf1eq w hw']; exact hb w hw'
          · have hz' : z ∈ U \ ((insert a s : Finset ℂ) : Set ℂ) := by
              refine ⟨hz.1, ?_⟩
              simp only [Finset.coe_insert, mem_insert_iff, not_or]
              exact ⟨hza, hz.2⟩
            rw [hf1eq z hz']; exact hb z hz'
        obtain ⟨F, hF, hFeq, hFb⟩ := ih f1 hd1 hbnd
        exact ⟨F, hF, fun z hz => by
          have hz1 : z ∈ U \ (s : Set ℂ) := ⟨hz.1, fun h => hz.2 (by simp [h])⟩
          rw [hFeq z hz1]; exact hf1eq z hz, hFb⟩
      · have hset : U \ ((insert a s : Finset ℂ) : Set ℂ) = U \ (s : Set ℂ) := by
          ext z
          simp only [Set.mem_sdiff, Finset.coe_insert, mem_insert_iff, not_or]
          constructor
          · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩
            refine ⟨h1, fun hza => haU ⟨hza ▸ h1, hza ▸ h3⟩, h3⟩
        rw [hset] at hd hb
        obtain ⟨F, hF, hFeq, hFb⟩ := ih f hd hb
        exact ⟨F, hF, fun z hz => hFeq z (hset ▸ hz), hFb⟩


/-! ### The parameters of the normal form -/

/-- `θ₀² = 12 α̃ / π²`. -/
noncomputable def o4Theta0Sq (L : ℝ) : ℝ := 12 / π ^ 2 * edgeAlphaTilde L

/-- `θ₀ = (2 √3 / π) α̃^{1/2}`, the positive critical point of `Φ_mod`. -/
noncomputable def o4Theta0 (L : ℝ) : ℝ := Real.sqrt (o4Theta0Sq L)

/-- `σ₀ = τ₀ / θ₀`. -/
noncomputable def o4Sigma0 (L : ℝ) : ℝ := tau0 L / o4Theta0 L

/-- The cubic model phase `Φ_mod(θ) = α̃ θ - π² θ³ / 36`. -/
noncomputable def o4PhiMod (L : ℝ) (θ : ℂ) : ℂ := (edgeAlphaTilde L : ℂ) * θ - (π : ℂ) ^ 2 / 36 * θ ^ 3

/-- `Φ̂(θ) = Φ_L(σ₀ θ)`. -/
noncomputable def o4PhiHat (L : ℝ) (θ : ℂ) : ℂ := edgePhiC L ((o4Sigma0 L : ℂ) * θ)

/-- The paper's quotient `𝓕(θ) = (Φ̂ - Φ_mod) / (θ (θ² - θ₀²)²)` (junk value at its three singularities). -/
noncomputable def o4Quot (L : ℝ) (θ : ℂ) : ℂ :=
  (o4PhiHat L θ - o4PhiMod L θ) / (θ * (θ ^ 2 - (o4Theta0Sq L : ℂ)) ^ 2)

/-- **Named hypothesis** (the paper's `M_F ≤ 0.13`, `[O4C (B)]`): `‖𝓕‖ ≤ 0.13` on `D(0, 0.25)` away from the
removable singularities `0, ±θ₀`. -/
def O4QuotientBound (L : ℝ) : Prop :=
  ∀ θ : ℂ, ‖θ‖ < 0.25 → θ ≠ 0 → θ ≠ (o4Theta0 L : ℂ) → θ ≠ -(o4Theta0 L : ℂ) → ‖o4Quot L θ‖ ≤ 0.13

section params

variable {L : ℝ}

lemma o4Theta0Sq_pos (hL : 0 < L) : 0 < o4Theta0Sq L := by
  unfold o4Theta0Sq; have := edgeAlphaTilde_pos hL; positivity

lemma o4Theta0Sq_le (hL0 : 0 < L) (hL2 : L ≤ 0.002) : o4Theta0Sq L ≤ 0.00244 := by
  have hκ := edgeKappa0_bounds hL0 hL2
  have hα : edgeAlphaTilde L ≤ L * (1 + L / 4) := by
    have := hκ.2; unfold edgeKappa0 at this
    rw [div_le_iff₀ hL0] at this; linarith
  have hpi : (3.14 : ℝ) < π := Real.pi_gt_d2
  unfold o4Theta0Sq
  have h12 : 12 / π ^ 2 ≤ 1.2173 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  calc 12 / π ^ 2 * edgeAlphaTilde L ≤ 1.2173 * (L * (1 + L / 4)) :=
        mul_le_mul h12 hα (edgeAlphaTilde_pos hL0).le (by norm_num)
    _ ≤ 0.00244 := by nlinarith

lemma o4Theta0_pos (hL : 0 < L) : 0 < o4Theta0 L := Real.sqrt_pos.mpr (o4Theta0Sq_pos hL)

lemma o4Theta0_sq (hL : 0 < L) : o4Theta0 L ^ 2 = o4Theta0Sq L :=
  Real.sq_sqrt (o4Theta0Sq_pos hL).le

lemma o4Theta0_lt (hL0 : 0 < L) (hL2 : L ≤ 0.002) : o4Theta0 L < 0.05 := by
  have h := o4Theta0Sq_le hL0 hL2
  rw [← abs_of_pos (o4Theta0_pos hL0)]
  apply abs_lt_of_sq_lt_sq _ (by norm_num)
  rw [o4Theta0_sq hL0]; linarith

lemma o4Sigma0_pos (hL : 0 < L) : 0 < o4Sigma0 L := div_pos (tau0_pos hL) (o4Theta0_pos hL)

lemma o4Sigma0_mul (hL : 0 < L) : o4Sigma0 L * o4Theta0 L = tau0 L := by
  unfold o4Sigma0; field_simp [(o4Theta0_pos hL).ne']

lemma o4Sigma0_le (hL0 : 0 < L) (hL2 : L ≤ 0.002) : o4Sigma0 L ≤ 1.003 := by
  have hb := tau0_bounds hL0 hL2
  have hτ := tau0_pos hL0
  have hκ := edgeKappa0_bounds hL0 hL2
  have hα : L ≤ edgeAlphaTilde L := by
    have := hκ.1; unfold edgeKappa0 at this
    rw [lt_div_iff₀ hL0] at this; linarith
  have hpi : π < 3.1416 := Real.pi_lt_d4
  have hθ : (12 / π ^ 2) * L ≤ o4Theta0Sq L := by
    unfold o4Theta0Sq; exact mul_le_mul_of_nonneg_left hα (by positivity)
  have hτ2 : tau0 L ^ 2 ≤ 1.105 ^ 2 * L := by
    calc tau0 L ^ 2 ≤ (1.105 * Real.sqrt L) ^ 2 := by gcongr; exact hb.2.1
      _ = 1.105 ^ 2 * L := by rw [mul_pow, Real.sq_sqrt hL0.le]
  have hσ2 : o4Sigma0 L ^ 2 ≤ 1.006 := by
    unfold o4Sigma0
    rw [div_pow, o4Theta0_sq hL0, div_le_iff₀ (o4Theta0Sq_pos hL0)]
    have h1 : 1.006 * ((12 / π ^ 2) * L) ≥ 1.105 ^ 2 * L := by
      have : 1.105 ^ 2 * π ^ 2 ≤ 1.006 * 12 := by nlinarith [Real.pi_pos]
      have h2 : 1.105 ^ 2 ≤ 1.006 * 12 / π ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact this
      calc 1.105 ^ 2 * L ≤ (1.006 * 12 / π ^ 2) * L := mul_le_mul_of_nonneg_right h2 hL0.le
        _ = 1.006 * ((12 / π ^ 2) * L) := by ring
    nlinarith
  nlinarith [o4Sigma0_pos hL0]

end params


/-! ### The vanishing of `Φ̂ - Φ_mod` at `0, ±θ₀` and the holomorphic quotient -/

section quotient

variable {L : ℝ}

lemma o4_sigma_norm_lt (hL0 : 0 < L) (hL2 : L ≤ 0.002) {θ : ℂ} (hθ : ‖θ‖ < 0.25) :
    ‖(o4Sigma0 L : ℂ) * θ‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (o4Sigma0_pos hL0)]
  have h := o4Sigma0_le hL0 hL2
  nlinarith [norm_nonneg θ]

lemma o4PhiMod_neg (θ : ℂ) : o4PhiMod L (-θ) = -o4PhiMod L θ := by
  unfold o4PhiMod; ring

lemma o4PhiHat_neg (hL0 : 0 < L) (hL2 : L ≤ 0.002) {θ : ℂ} (hθ : ‖θ‖ < 0.25) :
    o4PhiHat L (-θ) = -o4PhiHat L θ := by
  unfold o4PhiHat
  rw [mul_neg, edgePhiC_neg L (o4_sigma_norm_lt hL0 hL2 hθ)]

lemma o4Theta0_eq (hL : 0 < L) : o4Theta0 L = 2 * Real.sqrt 3 / π * Real.sqrt (edgeAlphaTilde L) := by
  have hα := edgeAlphaTilde_pos hL
  have hpi := Real.pi_pos
  have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  unfold o4Theta0 o4Theta0Sq
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  have e1 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have e2 : Real.sqrt (edgeAlphaTilde L) * Real.sqrt (edgeAlphaTilde L) = edgeAlphaTilde L := Real.mul_self_sqrt hα.le
  field_simp
  nlinarith [e1, e2]

/-- `Φ̂(θ₀) = Φ_mod(θ₀)`: both equal `(4√3/(3π)) α̃^{3/2}` (definition of `α̃`). -/
lemma o4PhiHat_theta0 (hL0 : 0 < L) (hL2 : L ≤ 0.002) :
    o4PhiHat L (o4Theta0 L : ℂ) = o4PhiMod L (o4Theta0 L : ℂ) := by
  have hα := edgeAlphaTilde_pos hL0
  have hpi := Real.pi_pos
  have hτ := tau0_bounds hL0 hL2
  have hτ0 := tau0_pos hL0
  have hσ : (o4Sigma0 L : ℂ) * (o4Theta0 L : ℂ) = (tau0 L : ℂ) := by exact_mod_cast o4Sigma0_mul hL0
  have hlt : |tau0 L| < 1 := by rw [abs_of_pos hτ0]; linarith [hτ.1]
  unfold o4PhiHat
  rw [hσ, edgePhiC_ofReal L hlt, ← edgeAlphaTilde_eq hL0]
  unfold o4PhiMod
  have hθ := o4Theta0_eq hL0
  have hsq := o4Theta0_sq hL0
  have hr : edgeAlphaTilde L ^ (3 / 2 : ℝ) = edgeAlphaTilde L * Real.sqrt (edgeAlphaTilde L) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hα, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hr]
  have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  have hthsq : (π : ℝ) ^ 2 * o4Theta0 L ^ 2 = 12 * edgeAlphaTilde L := by
    rw [hsq]; unfold o4Theta0Sq; field_simp
  have : (edgeAlphaTilde L : ℝ) * o4Theta0 L - π ^ 2 / 36 * o4Theta0 L ^ 3 =
      4 * Real.sqrt 3 / (3 * π) * (edgeAlphaTilde L * Real.sqrt (edgeAlphaTilde L)) := by
    have e : π ^ 2 / 36 * o4Theta0 L ^ 3 = o4Theta0 L * (π ^ 2 * o4Theta0 L ^ 2) / 36 := by ring
    rw [e, hthsq]
    conv_lhs => rw [hθ]
    field_simp
    ring
  exact_mod_cast this.symm

lemma o4PhiHat_zero : o4PhiHat L 0 = 0 := by simp [o4PhiHat, edgePhiC_zero]
lemma o4PhiMod_zero : o4PhiMod L 0 = 0 := by simp [o4PhiMod]


lemma differentiableOn_o4PhiHat (hL0 : 0 < L) (hL2 : L ≤ 0.002) :
    DifferentiableOn ℂ (o4PhiHat L) (ball 0 0.25) := fun θ hθ => by
  rw [mem_ball_zero_iff] at hθ
  have h1 := hasDerivAt_edgePhiC L (o4_sigma_norm_lt hL0 hL2 hθ)
  have h2 : HasDerivAt (fun w : ℂ => (o4Sigma0 L : ℂ) * w) (o4Sigma0 L : ℂ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (o4Sigma0 L : ℂ)
  exact ((h1.comp θ h2).differentiableAt).differentiableWithinAt

lemma differentiableOn_o4PhiMod : DifferentiableOn ℂ (o4PhiMod L) univ := by
  unfold o4PhiMod; fun_prop

/-- Holomorphic extension of the quotient `𝓕` to `D(0, 0.25)` with the bound `0.13`, and the identity
`Φ̂ - Φ_mod = θ (θ² - θ₀²)² 𝓕`. Under the named hypothesis `O4QuotientBound`. -/
theorem o4_quotient_ext (hL0 : 0 < L) (hL2 : L ≤ 0.002) (hM : O4QuotientBound L) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball 0 0.25) ∧ (∀ θ ∈ ball (0 : ℂ) 0.25, ‖F θ‖ ≤ 0.13) ∧
      (∀ θ ∈ ball (0 : ℂ) 0.25, o4PhiHat L θ - o4PhiMod L θ =
        θ * (θ ^ 2 - (o4Theta0Sq L : ℂ)) ^ 2 * F θ) ∧
      (∀ θ ∈ ball (0 : ℂ) 0.25, F (-θ) = F θ) ∧
      (∀ θ ∈ ball (0 : ℂ) 0.25, F ((starRingEnd ℂ) θ) = (starRingEnd ℂ) (F θ)) := by
  classical
  set t0 : ℝ := o4Theta0 L with ht0
  have ht0pos : 0 < t0 := o4Theta0_pos hL0
  have ht0sq : (t0 : ℂ) ^ 2 = (o4Theta0Sq L : ℂ) := by exact_mod_cast o4Theta0_sq hL0
  let pts : Finset ℂ := {0, (t0 : ℂ), -(t0 : ℂ)}
  have hpts : ∀ z : ℂ, z ∉ (pts : Set ℂ) ↔ z ≠ 0 ∧ z ≠ t0 ∧ z ≠ -t0 := fun z => by
    simp [pts]
  have hden : ∀ z : ℂ, z ∉ (pts : Set ℂ) → z * (z ^ 2 - (o4Theta0Sq L : ℂ)) ^ 2 ≠ 0 := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := (hpts z).mp hz
    refine mul_ne_zero h1 (pow_ne_zero _ ?_)
    intro h
    rw [← ht0sq] at h
    have : (z - t0) * (z + t0) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h | h
    · exact h2 (sub_eq_zero.mp h)
    · exact h3 (eq_neg_of_add_eq_zero_left h)
  have hdiff : DifferentiableOn ℂ (o4Quot L) (ball 0 0.25 \ (pts : Set ℂ)) := by
    refine DifferentiableOn.div ?_ ?_ fun z hz => hden z hz.2
    · exact ((differentiableOn_o4PhiHat hL0 hL2).mono Set.sdiff_subset).sub
        (differentiableOn_o4PhiMod.mono (subset_univ _))
    · fun_prop
  have hb : ∀ z ∈ ball (0 : ℂ) 0.25 \ (pts : Set ℂ), ‖o4Quot L z‖ ≤ 0.13 := fun z hz => by
    obtain ⟨h1, h2, h3⟩ := (hpts z).mp hz.2
    exact hM z (by simpa using hz.1) h1 h2 h3
  obtain ⟨F, hF, hFeq, hFb⟩ := removable_finite isOpen_ball 0.13 pts _ hdiff hb
  have hid : ∀ θ ∈ ball (0 : ℂ) 0.25, o4PhiHat L θ - o4PhiMod L θ =
      θ * (θ ^ 2 - (o4Theta0Sq L : ℂ)) ^ 2 * F θ := by
    intro θ hθ
    by_cases hz : θ ∈ (pts : Set ℂ)
    · have hθ' : ‖θ‖ < 0.25 := by simpa using hθ
      have hneg0 := o4PhiHat_theta0 hL0 hL2
      have hzcases : θ = 0 ∨ θ = t0 ∨ θ = -t0 := by simpa [pts] using hz
      rcases hzcases with h | h | h
      · subst h; simp [o4PhiHat_zero, o4PhiMod_zero]
      · subst h
        rw [hneg0, sub_self, ← ht0sq]; ring
      · subst h
        have hn : ‖(t0 : ℂ)‖ < 0.25 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0pos]
          linarith [o4Theta0_lt hL0 hL2]
        rw [o4PhiHat_neg hL0 hL2 hn, o4PhiMod_neg, hneg0, sub_self, neg_sq, ← ht0sq]; ring
    · rw [hFeq θ ⟨hθ, hz⟩]
      unfold o4Quot
      have := hden θ hz
      have h2 := div_mul_cancel₀ (o4PhiHat L θ - o4PhiMod L θ) this
      linear_combination -h2
  have hdense : ball (0 : ℂ) 0.25 ⊆ closure (ball (0 : ℂ) 0.25 \ (pts : Set ℂ)) := by
    have hd : Dense ((pts : Set ℂ)ᶜ) := (pts.countable_toSet).dense_compl ℝ
    have := hd.open_subset_closure_inter (isOpen_ball (x := (0 : ℂ)) (ε := 0.25))
    rwa [← Set.sdiff_eq] at this
  refine ⟨F, hF, fun θ hθ => hFb θ hθ, hid, ?_, ?_⟩
  swap
  · -- reflection symmetry
    have hmemc : ∀ θ ∈ ball (0 : ℂ) 0.25, (starRingEnd ℂ) θ ∈ ball (0 : ℂ) 0.25 := fun θ hθ => by simpa using hθ
    have hEqc : EqOn (fun θ => F ((starRingEnd ℂ) θ)) (fun θ => (starRingEnd ℂ) (F θ)) (ball (0 : ℂ) 0.25 \ (pts : Set ℂ)) := by
      intro θ hθ
      have hθ' : (starRingEnd ℂ) θ ∈ ball (0 : ℂ) 0.25 \ (pts : Set ℂ) := by
        refine ⟨hmemc θ hθ.1, ?_⟩
        obtain ⟨h1, h2, h3⟩ := (hpts θ).mp hθ.2
        rw [hpts]
        refine ⟨by simpa using h1, fun h => h2 ?_, fun h => h3 ?_⟩
        · have := congrArg (starRingEnd ℂ) h; simpa [Complex.conj_ofReal] using this
        · have := congrArg (starRingEnd ℂ) h; simpa [Complex.conj_ofReal] using this
      simp only
      rw [hFeq _ hθ', hFeq θ hθ]
      have hnorm : ‖θ‖ < 0.25 := by simpa using hθ.1
      have hn2 : ‖(starRingEnd ℂ) θ‖ < 0.25 := by simpa using hnorm
      unfold o4Quot o4PhiHat o4PhiMod
      have hc1 : (o4Sigma0 L : ℂ) * (starRingEnd ℂ) θ = (starRingEnd ℂ) ((o4Sigma0 L : ℂ) * θ) := by
        simp [map_mul, Complex.conj_ofReal]
      rw [hc1, edgePhiC_conj L (o4_sigma_norm_lt hL0 hL2 hnorm)]
      simp [map_sub, map_mul, map_div₀, map_pow, Complex.conj_ofReal, map_ofNat]
    have hc1 : ContinuousOn (fun θ => F ((starRingEnd ℂ) θ)) (ball (0 : ℂ) 0.25) :=
      hF.continuousOn.comp Complex.continuous_conj.continuousOn (fun θ hθ => hmemc θ hθ)
    have hc2 : ContinuousOn (fun θ => (starRingEnd ℂ) (F θ)) (ball (0 : ℂ) 0.25) :=
      Complex.continuous_conj.comp_continuousOn hF.continuousOn
    intro θ hθ
    exact (Set.EqOn.of_subset_closure hEqc hc1 hc2 Set.sdiff_subset hdense) hθ

  -- evenness: both sides continuous, equal off the three points, which are nowhere dense
  have hmem : ∀ θ ∈ ball (0 : ℂ) 0.25, -θ ∈ ball (0 : ℂ) 0.25 := fun θ hθ => by simpa using hθ
  have hEq : EqOn (fun θ => F (-θ)) F (ball (0 : ℂ) 0.25 \ (pts : Set ℂ)) := by
    intro θ hθ
    have hθ' : -θ ∈ ball (0 : ℂ) 0.25 \ (pts : Set ℂ) := by
      refine ⟨hmem θ hθ.1, ?_⟩
      obtain ⟨h1, h2, h3⟩ := (hpts θ).mp hθ.2
      rw [hpts]
      exact ⟨neg_ne_zero.mpr h1, fun h => h3 (by rw [← neg_eq_iff_eq_neg.mp h]) |>.elim,
        fun h => h2 (by rw [neg_eq_iff_eq_neg.mp h]; simp) |>.elim⟩
    simp only
    rw [hFeq _ hθ', hFeq θ hθ]
    have hnorm : ‖θ‖ < 0.25 := by simpa using hθ.1
    unfold o4Quot
    rw [show (-θ) ^ 2 = θ ^ 2 by ring, o4PhiHat_neg hL0 hL2 hnorm, o4PhiMod_neg]
    have := hden θ hθ.2
    field_simp
    ring
  have hdense : ball (0 : ℂ) 0.25 ⊆ closure (ball (0 : ℂ) 0.25 \ (pts : Set ℂ)) := by
    have hd : Dense ((pts : Set ℂ)ᶜ) := (pts.countable_toSet).dense_compl ℝ
    have := hd.open_subset_closure_inter (isOpen_ball (x := (0 : ℂ)) (ε := 0.25))
    rwa [← Set.sdiff_eq] at this
  have hc1 : ContinuousOn (fun θ => F (-θ)) (ball (0 : ℂ) 0.25) :=
    hF.continuousOn.comp continuous_neg.continuousOn (fun θ hθ => hmem θ hθ)
  intro θ hθ
  exact (Set.EqOn.of_subset_closure hEq hc1 hF.continuousOn Set.sdiff_subset hdense) hθ

end quotient

/-! ### The normal-form map `τ(θ)` -/

/-- The algebra of the fixed-point reduction (`[O4C (B)]`): with `ψ = θ(1 + pη)`, `p = θ² - t`,
`Q = 1 + 2θ²η + θ²pη²` and `α̃ = π² t / 12`,
`Φ_mod(ψ) + ψ(ψ² - t)² F - Φ_mod(θ) = θ p² (π²/12) (𝒯(η) - η)`. -/
lemma o4_algebra (θ η t F : ℂ) (hpi : (π : ℂ) ≠ 0) :
    ((π : ℂ) ^ 2 / 12 * t * (θ * (1 + (θ ^ 2 - t) * η) - θ)
        - (π : ℂ) ^ 2 / 36 * ((θ * (1 + (θ ^ 2 - t) * η)) ^ 3 - θ ^ 3))
      + (θ * (1 + (θ ^ 2 - t) * η)) * ((θ * (1 + (θ ^ 2 - t) * η)) ^ 2 - t) ^ 2 * F
    = θ * (θ ^ 2 - t) ^ 2 * ((π : ℂ) ^ 2 / 12) *
      (((12 / (π : ℂ) ^ 2) * ((1 + (θ ^ 2 - t) * η) *
        (1 + 2 * θ ^ 2 * η + θ ^ 2 * (θ ^ 2 - t) * η ^ 2) ^ 2 * F)
        - θ ^ 2 * η ^ 2 - θ ^ 2 * (θ ^ 2 - t) * η ^ 3 / 3) - η) := by
  field_simp
  ring

/-- The conclusions of Lemma `O.4(2)` for a map `τ` (see `o4_normal_form`). -/
structure O4NormalForm (L : ℝ) (τ : ℂ → ℂ) : Prop where
  differentiableOn : DifferentiableOn ℂ τ (ball 0 0.22)
  zero : τ 0 = 0
  norm_lt : ∀ θ ∈ ball (0 : ℂ) 0.22, ‖τ θ‖ < 0.45
  phase : ∀ θ ∈ ball (0 : ℂ) 0.22, edgePhiC L (τ θ) = o4PhiMod L θ
  at_theta0 : τ (o4Theta0 L : ℂ) = (tau0 L : ℂ)
  at_neg_theta0 : τ (-(o4Theta0 L : ℂ)) = -(tau0 L : ℂ)
  odd : ∀ θ ∈ ball (0 : ℂ) 0.22, τ (-θ) = -τ θ
  hasDerivAt_zero : HasDerivAt τ (edgeKappa0 L : ℂ) 0
  /-- the fixed-point profile `η`, `‖η‖ ≤ 1/5`, with `τ = σ₀ θ (1 + (θ² - θ₀²) η)` -/
  eta : ∃ η : ℂ → ℂ, DifferentiableOn ℂ η (ball 0 0.22) ∧
    ∀ θ ∈ ball (0 : ℂ) 0.22, ‖η θ‖ ≤ 1 / 5 ∧
      τ θ = (o4Sigma0 L : ℂ) * (θ * (1 + (θ ^ 2 - (o4Theta0Sq L : ℂ)) * η θ))
  real : ∀ θ : ℝ, |θ| < 0.22 → (starRingEnd ℂ) (τ (θ : ℂ)) = τ (θ : ℂ)

/-- **Lemma `O.4(2)` (`u1co:O4`), existence and normal form, under the named hypothesis
`O4QuotientBound L` (`M_F ≤ 0.13`).** For `L ∈ (0, 0.002]` there is a holomorphic `τ` on `D(0, 0.22)` with
`τ(0) = 0`, `|τ| < 0.45`, `Φ_L(τ(θ)) = Φ_mod(θ)`, `τ(±θ₀) = ±τ₀`, `τ` odd, real on `ℝ` and `τ'(0) = κ₀`. -/
theorem o4_normal_form {L : ℝ} (hL0 : 0 < L) (hL2 : L ≤ 0.002) (hM : O4QuotientBound L) :
    ∃ τ : ℂ → ℂ, O4NormalForm L τ := by
  obtain ⟨F, hFd, hFb, hFid, hFe, hFc⟩ := o4_quotient_ext hL0 hL2 hM
  have hth0 := o4Theta0Sq_pos hL0
  obtain ⟨η, hηd, hηfix, hηuniq⟩ := o4_fixed_point (θ0sq := o4Theta0Sq L) hth0.le
    (o4Theta0Sq_le hL0 hL2) hFd hFb
  have hηe : ∀ θ ∈ ball (0 : ℂ) 0.22, η (-θ) = η θ := by
    refine o4_fixed_point_even (F := F) hth0.le (o4Theta0Sq_le hL0 hL2)
      (fun z hz => hFe z hz) (fun θ hθ => hηfix θ hθ) hηuniq
  set σ : ℝ := o4Sigma0 L with hσ
  set t : ℝ := o4Theta0Sq L with ht
  let τ : ℂ → ℂ := fun θ => (σ : ℂ) * (θ * (1 + (θ ^ 2 - (t : ℂ)) * η θ))
  have hτ0 : ∀ θ ∈ ball (0 : ℂ) 0.22, ‖θ * (1 + (θ ^ 2 - (t : ℂ)) * η θ)‖ ≤ 0.2223 := fun θ hθ =>
    (o4_bounds hth0.le (o4Theta0Sq_le hL0 hL2) (by simpa using hθ) (hηfix θ hθ).1).2.2.2.2.2
  have hσle := o4Sigma0_le hL0 hL2
  have hσpos := o4Sigma0_pos hL0
  have hτb : ∀ θ ∈ ball (0 : ℂ) 0.22, ‖τ θ‖ < 0.45 := fun θ hθ => by
    simp only [τ]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσpos]
    have := hτ0 θ hθ
    nlinarith [norm_nonneg (θ * (1 + (θ ^ 2 - (t : ℂ)) * η θ))]
  have ht0lt := o4Theta0_lt hL0 hL2
  have ht0pos := o4Theta0_pos hL0
  have ht0sq : (o4Theta0 L : ℂ) ^ 2 = (t : ℂ) := by exact_mod_cast o4Theta0_sq hL0
  have hmem0 : (o4Theta0 L : ℂ) ∈ ball (0 : ℂ) 0.22 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0pos]; linarith
  have hmem0' : -(o4Theta0 L : ℂ) ∈ ball (0 : ℂ) 0.22 := by simpa using hmem0
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hα : (edgeAlphaTilde L : ℂ) = (π : ℂ) ^ 2 / 12 * (t : ℂ) := by
    have hpi' : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have : edgeAlphaTilde L = π ^ 2 / 12 * o4Theta0Sq L := by
      unfold o4Theta0Sq; field_simp
    rw [this]; push_cast; ring
  have hτdiff : DifferentiableOn ℂ τ (ball 0 0.22) :=
    ((differentiableOn_id.mul (differentiableOn_const _ |>.add
      (((differentiableOn_id.pow 2).sub (differentiableOn_const _)).mul hηd)))).const_mul _
  have hτ00 : τ 0 = 0 := by simp [τ]
  have hσθ : (σ : ℂ) * (o4Theta0 L : ℂ) = (tau0 L : ℂ) := by exact_mod_cast o4Sigma0_mul hL0
  have hPhi : ∀ θ ∈ ball (0 : ℂ) 0.22, edgePhiC L (τ θ) = o4PhiMod L θ := by
    intro θ hθ
    have hψ := hτ0 θ hθ
    have hψ' : (θ * (1 + (θ ^ 2 - (t : ℂ)) * η θ)) ∈ ball (0 : ℂ) 0.25 := by
      rw [mem_ball_zero_iff]; linarith
    have h1 := hFid _ hψ'
    have hfix := (hηfix θ hθ).2
    have key := o4_algebra θ (η θ) (t : ℂ) (F (θ * (1 + (θ ^ 2 - (t : ℂ)) * η θ))) hpi
    have hrhs : ((12 / (π : ℂ) ^ 2) * ((1 + (θ ^ 2 - (t : ℂ)) * η θ) *
        (1 + 2 * θ ^ 2 * η θ + θ ^ 2 * (θ ^ 2 - (t : ℂ)) * η θ ^ 2) ^ 2 *
          F (θ * (1 + (θ ^ 2 - (t : ℂ)) * η θ)))
        - θ ^ 2 * η θ ^ 2 - θ ^ 2 * (θ ^ 2 - (t : ℂ)) * η θ ^ 3 / 3) - η θ = 0 := by
      have : o4G t F θ (η θ) = (12 / (π : ℂ) ^ 2) * ((1 + (θ ^ 2 - (t : ℂ)) * η θ) *
        (1 + 2 * θ ^ 2 * η θ + θ ^ 2 * (θ ^ 2 - (t : ℂ)) * η θ ^ 2) ^ 2 *
          F (θ * (1 + (θ ^ 2 - (t : ℂ)) * η θ)))
        - θ ^ 2 * η θ ^ 2 - θ ^ 2 * (θ ^ 2 - (t : ℂ)) * η θ ^ 3 / 3 := by
        unfold o4G; push_cast; ring
      rw [← this, ← hfix]; ring
    rw [hrhs, mul_zero] at key
    have hΦ : edgePhiC L (τ θ) = o4PhiHat L (θ * (1 + (θ ^ 2 - (t : ℂ)) * η θ)) := rfl
    rw [hΦ]
    have h2 : o4PhiMod L (θ * (1 + (θ ^ 2 - (t : ℂ)) * η θ)) - o4PhiMod L θ =
        (π : ℂ) ^ 2 / 12 * t * (θ * (1 + (θ ^ 2 - (t : ℂ)) * η θ) - θ)
        - (π : ℂ) ^ 2 / 36 * ((θ * (1 + (θ ^ 2 - (t : ℂ)) * η θ)) ^ 3 - θ ^ 3) := by
      unfold o4PhiMod; rw [hα]; ring
    linear_combination h1 + h2 + key
  have hderiv : HasDerivAt τ (edgeKappa0 L : ℂ) 0 := by
    have hball : ball (0 : ℂ) 0.22 ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds (mem_ball_self (by norm_num))
    have hτd : HasDerivAt τ (deriv τ 0) 0 := (hτdiff.differentiableAt hball).hasDerivAt
    have hΦd := hasDerivAt_edgePhiC L (τ := τ 0) (by rw [hτ00]; simp)
    have hcomp : HasDerivAt (edgePhiC L ∘ τ) (((L : ℂ) + stripG (Complex.I * τ 0)) * deriv τ 0) 0 :=
      HasDerivAt.comp (0 : ℂ) hΦd hτd
    have hmod : HasDerivAt (o4PhiMod L) ((edgeAlphaTilde L : ℂ) - (π : ℂ) ^ 2 / 36 * (3 * 0 ^ 2)) 0 := by
      unfold o4PhiMod
      have h1 : HasDerivAt (fun θ : ℂ => (edgeAlphaTilde L : ℂ) * θ) (edgeAlphaTilde L : ℂ) 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).const_mul (edgeAlphaTilde L : ℂ)
      have h2 : HasDerivAt (fun θ : ℂ => (π : ℂ) ^ 2 / 36 * θ ^ 3) ((π : ℂ) ^ 2 / 36 * (3 * 0 ^ 2)) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).pow 3).const_mul ((π : ℂ) ^ 2 / 36)
      exact h1.sub h2
    have hmod' : HasDerivAt (edgePhiC L ∘ τ) ((edgeAlphaTilde L : ℂ) - (π : ℂ) ^ 2 / 36 * (3 * 0 ^ 2)) 0 :=
      hmod.congr_of_eventuallyEq (by
        filter_upwards [hball] with θ hθ
        exact hPhi θ hθ)
    have heq := hcomp.unique hmod'
    rw [hτ00] at heq
    have hs : stripG (Complex.I * 0) = 0 := by simp [stripG]
    rw [hs] at heq
    have hL : (L : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
    have hd : deriv τ 0 = (edgeKappa0 L : ℂ) := by
      unfold edgeKappa0
      push_cast
      rw [eq_div_iff hL]
      linear_combination heq
    rw [hd] at hτd; exact hτd
  have hreal : ∀ θ : ℝ, |θ| < 0.22 → (starRingEnd ℂ) (τ (θ : ℂ)) = τ (θ : ℂ) := by
    intro θ hθ
    have hr : (starRingEnd ℂ) (η (θ : ℂ)) = η (θ : ℂ) :=
      o4_fixed_point_real (F := F) hth0.le (o4Theta0Sq_le hL0 hL2) hFc
        (fun θ hθ => hηfix θ hθ) hηuniq hθ
    simp only [τ]
    simp [map_mul, map_add, map_sub, map_pow, Complex.conj_ofReal, hr]
  refine ⟨τ, ⟨hτdiff, hτ00, hτb, hPhi, ?_, ?_, ?_, hderiv,
    ⟨η, hηd, fun θ hθ => ⟨(hηfix θ hθ).1, rfl⟩⟩, hreal⟩⟩
  · show (σ : ℂ) * ((o4Theta0 L : ℂ) * (1 + ((o4Theta0 L : ℂ) ^ 2 - (t : ℂ)) * η (o4Theta0 L : ℂ))) = _
    rw [ht0sq, sub_self, zero_mul, add_zero, mul_one, hσθ]
  · show (σ : ℂ) * (-(o4Theta0 L : ℂ) * (1 + ((-(o4Theta0 L : ℂ)) ^ 2 - (t : ℂ)) * η (-(o4Theta0 L : ℂ)))) = _
    rw [neg_sq, ht0sq, sub_self, zero_mul, add_zero, mul_one, mul_neg, hσθ]
  · intro θ hθ
    show (σ : ℂ) * (-θ * (1 + ((-θ) ^ 2 - (t : ℂ)) * η (-θ))) = -((σ : ℂ) * (θ * (1 + (θ ^ 2 - (t : ℂ)) * η θ)))
    rw [hηe θ hθ, neg_sq]; ring

lemma o4Sigma0_ge {L : ℝ} (hL0 : 0 < L) (hL2 : L ≤ 0.002) : 0.9997 ≤ o4Sigma0 L := by
  have hτ := tau0_pos hL0
  have hκ := edgeKappa0_bounds hL0 hL2
  have hα : edgeAlphaTilde L ≤ L * (1 + L / 4) := by
    have := hκ.2; unfold edgeKappa0 at this
    rw [div_le_iff₀ hL0] at this; linarith
  have hg := tau0_gt_sqrt hL0 hτ (ceEll_tau0 hL0)
  have hpi := Real.pi_pos
  have hτ2 : (12 / π ^ 2) * L < tau0 L ^ 2 := by
    have h0 : 0 ≤ (2 * Real.sqrt 3 / π) * Real.sqrt L := by positivity
    have := pow_lt_pow_left₀ hg h0 (by norm_num : (2 : ℕ) ≠ 0)
    calc (12 / π ^ 2) * L = ((2 * Real.sqrt 3 / π) * Real.sqrt L) ^ 2 := by
          rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sq_sqrt hL0.le]; ring
      _ < _ := this
  have hθ : o4Theta0Sq L ≤ (12 / π ^ 2) * (L * (1 + L / 4)) := by
    unfold o4Theta0Sq; exact mul_le_mul_of_nonneg_left hα (by positivity)
  have hσ2 : 0.9995 ≤ o4Sigma0 L ^ 2 := by
    unfold o4Sigma0
    rw [div_pow, o4Theta0_sq hL0, le_div_iff₀ (o4Theta0Sq_pos hL0)]
    have h12 : 0 < 12 / π ^ 2 := by positivity
    nlinarith [mul_pos h12 hL0]
  nlinarith [o4Sigma0_pos hL0]

/-- `O.4(3)`, ratio bounds, from the contraction ball: `0.989 < τ(θ)/θ < 1.013` for real `0 < |θ| < 0.22`
(stronger than the paper's `0.95 < τ/θ < 1.05` on `[0.08, 0.2]` and `0.59 < τ/θ < 1.42` near `0`). -/
theorem O4NormalForm.ratio {L : ℝ} {τ : ℂ → ℂ} (h : O4NormalForm L τ) (hL0 : 0 < L) (hL2 : L ≤ 0.002)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθ : |θ| < 0.22) :
    0.989 < (τ (θ : ℂ)).re / θ ∧ (τ (θ : ℂ)).re / θ < 1.013 := by
  obtain ⟨η, -, hη⟩ := h.eta
  have hmem : (θ : ℂ) ∈ ball (0 : ℂ) 0.22 := by simpa [Complex.norm_real] using hθ
  obtain ⟨hηb, hτeq⟩ := hη _ hmem
  have hreal : (τ (θ : ℂ)) = ((τ (θ : ℂ)).re : ℂ) := by
    have := h.real θ hθ
    exact (Complex.conj_eq_iff_re.mp this).symm
  set r : ℝ := (τ (θ : ℂ)).re / θ with hr
  have hrc : (r : ℂ) = (o4Sigma0 L : ℂ) * (1 + ((θ : ℂ) ^ 2 - (o4Theta0Sq L : ℂ)) * η θ) := by
    rw [hr]; push_cast
    rw [← hreal, hτeq]
    have : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0
    field_simp
  have hσ := o4Sigma0_pos hL0
  have hp : ‖((θ : ℂ) ^ 2 - (o4Theta0Sq L : ℂ))‖ ≤ 0.0484 := by
    have hts := o4Theta0Sq_le hL0 hL2
    have hth := o4Theta0Sq_pos hL0
    have h2 : (θ : ℝ) ^ 2 < 0.0484 := by nlinarith [abs_nonneg θ, sq_abs θ]
    rw [show ((θ : ℂ) ^ 2 - (o4Theta0Sq L : ℂ)) = ((θ ^ 2 - o4Theta0Sq L : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith
  have hd : |r - o4Sigma0 L| ≤ o4Sigma0 L * (0.0484 * (1 / 5)) := by
    have : ((r - o4Sigma0 L : ℝ) : ℂ) = (o4Sigma0 L : ℂ) *
        (((θ : ℂ) ^ 2 - (o4Theta0Sq L : ℂ)) * η θ) := by push_cast; rw [hrc]; ring
    rw [← Real.norm_eq_abs, ← Complex.norm_real, this, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hσ, norm_mul]
    gcongr
  have h1 := o4Sigma0_le hL0 hL2
  have h2 := o4Sigma0_ge hL0 hL2
  rw [abs_le] at hd
  constructor <;> nlinarith

/-- Cauchy estimate for the fixed-point profile: `‖η'‖ ≤ (1/5)/0.019` on `‖z‖ ≤ 0.2`. -/
lemma eta_deriv_bound {η : ℂ → ℂ} (hηd : DifferentiableOn ℂ η (ball 0 0.22))
    (hηb : ∀ θ ∈ ball (0 : ℂ) 0.22, ‖η θ‖ ≤ 1 / 5) {z : ℂ} (hz : ‖z‖ ≤ 0.2) :
    ‖deriv η z‖ ≤ (1 / 5) / 0.019 := by
  have hsub : closedBall z 0.019 ⊆ ball (0 : ℂ) 0.22 := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball_zero_iff]
    calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ < 0.22 := by linarith
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num)
    (hηd.diffContOnCl_ball hsub) fun w hw => hηb w (hsub (sphere_subset_closedBall hw))

/-- **Monotonicity of `τ` on the real axis (`O.4(2)`)**: `τ` is strictly increasing on `[-0.2, 0.2]`
(`τ' ≥ 0.88 σ₀ > 0`, from `‖η‖ ≤ 1/5` and the Cauchy estimate for `η'`). -/
theorem O4NormalForm.strictMonoOn {L : ℝ} {τ : ℂ → ℂ} (h : O4NormalForm L τ) (hL0 : 0 < L)
    (hL2 : L ≤ 0.002) : StrictMonoOn (fun θ : ℝ => (τ (θ : ℂ)).re) (Icc (-0.2) 0.2) := by
  obtain ⟨η, hηd, hη⟩ := h.eta
  have hηb : ∀ θ ∈ ball (0 : ℂ) 0.22, ‖η θ‖ ≤ 1 / 5 := fun θ hθ => (hη θ hθ).1
  have hσ := o4Sigma0_pos hL0
  have hts := o4Theta0Sq_le hL0 hL2
  have hth := o4Theta0Sq_pos hL0
  set t : ℝ := o4Theta0Sq L with ht
  have hball : ∀ x : ℝ, |x| < 0.22 → (x : ℂ) ∈ ball (0 : ℂ) 0.22 := fun x hx => by
    simpa [Complex.norm_real] using hx
  -- complex derivative of τ at a real point of `(-0.2, 0.2)`
  have hderiv : ∀ x : ℝ, x ∈ Ioo (-0.2 : ℝ) 0.2 → ∃ d : ℂ, HasDerivAt τ d (x : ℂ) ∧ 0 < d.re := by
    intro x hx
    have hxn : ‖(x : ℂ)‖ ≤ 0.2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith [hx.1, hx.2]
    have hxm : (x : ℂ) ∈ ball (0 : ℂ) 0.22 := hball x (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])
    have hηx : HasDerivAt η (deriv η x) x :=
      (hηd.differentiableAt (isOpen_ball.mem_nhds hxm)).hasDerivAt
    set e' := deriv η (x : ℂ)
    have hp : HasDerivAt (fun θ : ℂ => θ ^ 2 - (t : ℂ)) (2 * (x : ℂ)) x := by
      simpa using ((hasDerivAt_id (x : ℂ)).pow 2).sub_const (t : ℂ)
    have hg : HasDerivAt (fun θ : ℂ => (o4Sigma0 L : ℂ) * (θ * (1 + (θ ^ 2 - (t : ℂ)) * η θ)))
        ((o4Sigma0 L : ℂ) * ((1 + ((x : ℂ) ^ 2 - (t : ℂ)) * η x) +
          (x : ℂ) * (2 * (x : ℂ) * η x + ((x : ℂ) ^ 2 - (t : ℂ)) * e'))) x := by
      have h1 := ((hp.mul hηx).const_add 1)
      have h2 := (hasDerivAt_id (x : ℂ)).mul h1
      have h3 := h2.const_mul (o4Sigma0 L : ℂ)
      convert h3 using 1
      · funext θ; simp only [Pi.mul_apply, id]
      · simp only [Pi.mul_apply, id]; ring
    have hτg : HasDerivAt τ ((o4Sigma0 L : ℂ) * ((1 + ((x : ℂ) ^ 2 - (t : ℂ)) * η x) +
          (x : ℂ) * (2 * (x : ℂ) * η x + ((x : ℂ) ^ 2 - (t : ℂ)) * e'))) x := by
      refine hg.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds hxm] with θ hθ
      exact (hη θ hθ).2
    refine ⟨_, hτg, ?_⟩
    -- real part positive
    have hηx_b := hηb _ hxm
    have he' := eta_deriv_bound hηd hηb hxn
    set D : ℂ := (1 + ((x : ℂ) ^ 2 - (t : ℂ)) * η x) +
          (x : ℂ) * (2 * (x : ℂ) * η x + ((x : ℂ) ^ 2 - (t : ℂ)) * e') with hD
    have hxa : |x| ≤ 0.2 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    have hx2 : ‖(x : ℂ) ^ 2‖ ≤ 0.04 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]; nlinarith [abs_nonneg x]
    have hpn : ‖(x : ℂ) ^ 2 - (t : ℂ)‖ ≤ 0.04244 := by
      calc ‖(x : ℂ) ^ 2 - (t : ℂ)‖ ≤ ‖(x : ℂ) ^ 2‖ + ‖(t : ℂ)‖ := norm_sub_le _ _
        _ ≤ 0.04 + 0.00244 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hth]; linarith
        _ = 0.04244 := by norm_num
    have hDm : ‖D - 1‖ ≤ 0.12 := by
      have e1 : D - 1 = ((x : ℂ) ^ 2 - (t : ℂ)) * η x +
          (x : ℂ) * (2 * (x : ℂ) * η x + ((x : ℂ) ^ 2 - (t : ℂ)) * e') := by rw [hD]; ring
      have a1 : ‖((x : ℂ) ^ 2 - (t : ℂ)) * η x‖ ≤ 0.04244 * (1 / 5) := by
        rw [norm_mul]; exact mul_le_mul hpn hηx_b (norm_nonneg _) (by norm_num)
      have a2 : ‖(x : ℂ) * (2 * (x : ℂ) * η x + ((x : ℂ) ^ 2 - (t : ℂ)) * e')‖ ≤
          0.2 * (2 * 0.2 * (1 / 5) + 0.04244 * ((1 / 5) / 0.019)) := by
        rw [norm_mul]
        refine mul_le_mul hxn ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _) (by norm_num)
        · rw [norm_mul, norm_mul]
          have h2' : ‖(2 : ℂ)‖ = 2 := by simp
          rw [h2']; gcongr
        · rw [norm_mul]; exact mul_le_mul hpn he' (norm_nonneg _) (by norm_num)
      rw [e1]
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ 0.04244 * (1 / 5) + 0.2 * (2 * 0.2 * (1 / 5) + 0.04244 * ((1 / 5) / 0.019)) := add_le_add a1 a2
        _ ≤ 0.12 := by norm_num
    have hre : 0 < D.re := by
      have := Complex.abs_re_le_norm (D - 1)
      have h1 : -(0.12 : ℝ) ≤ (D - 1).re := by linarith [abs_le.mp (this.trans hDm)]
      simp only [Complex.sub_re, Complex.one_re] at h1
      linarith
    show 0 < ((o4Sigma0 L : ℂ) * D).re
    rw [Complex.re_ofReal_mul]; exact mul_pos hσ hre
  -- real derivative
  have hT : ∀ x ∈ interior (Icc (-0.2 : ℝ) 0.2), 0 < deriv (fun θ : ℝ => (τ (θ : ℂ)).re) x := by
    intro x hx
    rw [interior_Icc] at hx
    obtain ⟨d, hd, hpos⟩ := hderiv x hx
    have h3 : HasDerivAt (fun y : ℝ => (τ (y : ℂ)).re) d.re x := hd.real_of_complex
    rw [h3.deriv]; exact hpos
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ hT
  intro x hx
  have hxm : (x : ℂ) ∈ ball (0 : ℂ) 0.22 := hball x (by rw [abs_lt]; constructor <;> linarith [(Set.mem_Icc.mp hx).1, (Set.mem_Icc.mp hx).2])
  have hcont : ContinuousAt τ (x : ℂ) :=
    (h.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hxm)).continuousAt
  exact ((Complex.continuous_re.continuousAt.comp (hcont.comp Complex.continuous_ofReal.continuousAt))).continuousWithinAt

/-- info: 'FormalResearch.CohnElkies.removable_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms removable_finite

/-- info: 'FormalResearch.CohnElkies.o4_quotient_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4_quotient_ext

/-- info: 'FormalResearch.CohnElkies.o4_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4_normal_form

/-- info: 'FormalResearch.CohnElkies.O4NormalForm.ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms O4NormalForm.ratio

/-- info: 'FormalResearch.CohnElkies.O4NormalForm.strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms O4NormalForm.strictMonoOn

end FormalResearch.CohnElkies
