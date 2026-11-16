module

public import FormalResearch.Special.AiryCftCircle

/-!
# The residue formula on a circle for `H / f`, `f` entire with simple zeros

Generic complex analysis (the residue theorem for a circle, in the case Mathlib does not cover: simple poles of `H/f`):
under `CftCircleData f c s R` and `H` entire,

`∮_{|w|=R} H(w)/f(w) dw = 2πi Σ_{i ∈ s} H(c_i)/f'(c_i)`   (`cftCircle_residue`).

Proof: `f = Π(w - c_i) φ` (`CftCircleData.factor`); with `r_i = H(c_i)/f'(c_i)` and `P_i = Π_{j ≠ i}(w - c_j)` the entire
function `H - φ Σ_i r_i P_i` vanishes at every `c_j` (as `φ(c_j) P_j(c_j) = f'(c_j)`), so equals `Π(w - c_i) K`; hence
`H/f = K/φ + Σ r_i/(w - c_i)` on the circle, `K/φ` is holomorphic on the closed disc (Cauchy-Goursat), and
`∮ 1/(w - c_i) = 2πi`.  Used by `AiryCftDefect` with `H = g · Bi` (`Bi(a_n)/Ai'(a_n) = -1/(π Ai'(a_n)²)`).
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real

namespace FormalResearch.Special

lemma cftRes_integral_finset_sum {R : ℝ} {ι : Type*} (t : Finset ι) (g : ι → ℂ → ℂ)
    (hg : ∀ i ∈ t, CircleIntegrable (g i) 0 R) :
    CircleIntegrable (fun w => ∑ i ∈ t, g i w) 0 R ∧
      ∮ w in C(0, R), ∑ i ∈ t, g i w = ∑ i ∈ t, ∮ w in C(0, R), g i w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [CircleIntegrable, circleIntegral]
  | insert j t hj ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have hgj := hg j (Finset.mem_insert_self j t)
    have e : (fun w => ∑ i ∈ insert j t, g i w) = fun w => g j w + ∑ i ∈ t, g i w := by
      funext w; rw [Finset.sum_insert hj]
    rw [e]
    refine ⟨hgj.add h1, ?_⟩
    rw [circleIntegral.integral_add hgj h1, h2, Finset.sum_insert hj]

section residue

variable {f : ℂ → ℂ} {c : ℕ → ℂ} {s : Finset ℕ} {R : ℝ}

/-- `f'(c_i) = φ(c_i) Π_{j ≠ i}(c_i - c_j)`. -/
lemma cftRes_deriv_eq {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ)
    (hfe : ∀ w, f w = (∏ i ∈ s, (w - c i)) * φ w) {i : ℕ} (hi : i ∈ s) :
    deriv f (c i) = φ (c i) * ∏ j ∈ s.erase i, (c i - c j) := by
  classical
  set ψ : ℂ → ℂ := fun w => (∏ j ∈ s.erase i, (w - c j)) * φ w with hψ
  have hfe' : f = fun w => (w - c i) * ψ w := by
    funext w
    rw [hfe, ← Finset.mul_prod_erase s (fun j => w - c j) hi, hψ]; ring
  have hψd : Differentiable ℂ ψ := by
    refine Differentiable.mul ?_ hφ
    fun_prop
  have hder : HasDerivAt f (ψ (c i)) (c i) := by
    rw [hfe']
    have := ((hasDerivAt_id (c i)).sub_const (c i)).fun_mul (hψd (c i)).hasDerivAt
    simpa using this
  rw [hder.deriv, hψ]; ring

/-- **Residue formula on a circle.** -/
theorem cftCircle_residue (h : CftCircleData f c s R) {H : ℂ → ℂ} (hH : Differentiable ℂ H) :
    ∮ w in C(0, R), H w / f w = 2 * π * I * ∑ i ∈ s, H (c i) / deriv f (c i) := by
  classical
  obtain ⟨φ, hφ, hfe, hφne⟩ := h.factor
  have hR := h.radius_pos
  set r : ℕ → ℂ := fun i => H (c i) / deriv f (c i) with hr
  set P : ℕ → ℂ → ℂ := fun i w => ∏ j ∈ s.erase i, (w - c j) with hP
  set G : ℂ → ℂ := fun w => H w - φ w * ∑ i ∈ s, r i * P i w with hG
  have hPd : ∀ i, Differentiable ℂ (P i) := fun i => by rw [hP]; fun_prop
  have hGd : Differentiable ℂ G := by
    refine hH.sub (hφ.mul ?_)
    exact Differentiable.fun_sum fun i _ => (differentiable_const _).mul (hPd i)
  have hGz : ∀ j ∈ s, G (c j) = 0 := by
    intro j hj
    have hsum : ∑ i ∈ s, r i * P i (c j) = r j * P j (c j) := by
      refine Finset.sum_eq_single j (fun i hi hij => ?_) (fun hj' => absurd hj hj')
      have : P i (c j) = 0 := by
        rw [hP]; exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun e => hij e.symm, hj⟩) (sub_self _)
      rw [this, mul_zero]
    have hd := cftRes_deriv_eq hφ hfe hj
    have hdj := h.simple j hj
    rw [hG]; simp only
    rw [hsum]
    have : φ (c j) * (r j * P j (c j)) = H (c j) := by
      rw [hr]; simp only; rw [hP]; simp only
      rw [hd]
      have hne : φ (c j) * ∏ k ∈ s.erase j, (c j - c k) ≠ 0 := by rw [← hd]; exact hdj
      obtain ⟨hn1, hn2⟩ := mul_ne_zero_iff.mp hne
      field_simp
    rw [this, sub_self]
  obtain ⟨K, hK, hKe⟩ := cftCircle_factor c s h.inj G hGd hGz
  -- the identity on the circle
  have hsph : ∀ w ∈ sphere (0 : ℂ) R, H w / f w = K w / φ w + ∑ i ∈ s, r i * (w - c i)⁻¹ := by
    intro w hw
    have hn : ‖w‖ = R := by simpa using hw
    have hfw := h.ne_zero_sphere hn
    have hpw : (∏ i ∈ s, (w - c i)) ≠ 0 := by
      intro h0; apply hfw; rw [hfe, h0, zero_mul]
    have hφw : φ w ≠ 0 := by
      intro h0; apply hfw; rw [hfe, h0, mul_zero]
    have hHw : H w = (∏ i ∈ s, (w - c i)) * K w + φ w * ∑ i ∈ s, r i * P i w := by
      have := hKe w; rw [hG] at this; simp only at this; linear_combination this
    have hPi : ∀ i ∈ s, P i w = (∏ j ∈ s, (w - c j)) * (w - c i)⁻¹ := by
      intro i hi
      have hwi : w - c i ≠ 0 := fun h0 => hpw (Finset.prod_eq_zero hi h0)
      rw [hP]; simp only
      rw [← Finset.mul_prod_erase s (fun j => w - c j) hi]
      field_simp
    rw [hfe w, hHw]
    have : ∑ i ∈ s, r i * P i w = (∏ j ∈ s, (w - c j)) * ∑ i ∈ s, r i * (w - c i)⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hPi i hi]; ring
    rw [this]
    field_simp
  -- integrate
  have hKφ : DifferentiableOn ℂ (fun w => K w / φ w) (closedBall 0 R) := fun x hx =>
    ((hK x).div (hφ x) (hφne x (by simpa using hx))).differentiableWithinAt
  have hint1 : CircleIntegrable (fun w => K w / φ w) 0 R :=
    ContinuousOn.circleIntegrable hR.le (hKφ.continuousOn.mono sphere_subset_closedBall)
  have hint2 : ∀ i ∈ s, CircleIntegrable (fun w => r i * (w - c i)⁻¹) 0 R := by
    intro i hi
    refine ContinuousOn.circleIntegrable hR.le ?_
    refine continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ => ?_)
    have hn : ‖ζ‖ = R := by simpa using hζ
    intro h0; have : ζ = c i := sub_eq_zero.mp h0
    have := h.inside i hi
    rw [← ‹ζ = c i›, hn] at this; exact lt_irrefl _ this
  obtain ⟨hint3, hsum⟩ := cftRes_integral_finset_sum s (fun i w => r i * (w - c i)⁻¹) hint2
  rw [circleIntegral.integral_congr hR.le hsph, circleIntegral.integral_add hint1 hint3,
    DiffContOnCl.circleIntegral_eq_zero hR.le (hKφ.mono closure_ball_subset_closedBall |>.diffContOnCl), zero_add,
    hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball (by simpa using h.inside i hi)]
  rw [hr]; ring

end residue

/-- info: 'FormalResearch.Special.cftCircle_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.cftCircle_residue

end FormalResearch.Special
