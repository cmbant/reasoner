module

public import FormalResearch.SignUncertainty.UctAiryTransSmall

/-!
# Scaled derivative asymptotics of `F̃_*`, `g̃₁`, `φ_{c,δ}` on the half plane (`uct:airy-trans` (2), F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:airy-trans` (2), `(uct:Fstar-asym)` and `(uct:phicd-bnds)`.

The derivatives on `{Re w ≥ 0}` are `iteratedDerivWithin` of the functions defined by the integral formula; they coincide with the
derivatives of the holomorphic extensions (`iteratedDerivWithin_halfplane_eq`).

* `uct_airy_trans_asymp_Fstar`: `∂_w^r (w^{5/2} F̃_*(i c_s w) - C_Ai) = O_r(|w|^{-2-r})` on `Re w ≥ 0`, `|w| ≥ 2`.
* `uct_airy_trans_asymp_g1`: `∂_w^r g̃₁(i c_s w) = O_r(|w|^{-9/2-r})`.
* `uct_airy_trans_phi`: `∂_w^r (φ_{c,δ} - 1) = O_r(c^{-2/3} |w|^{-2-r})` for `0 < c`, `0 ≤ δ ≤ 1`, `|w| ≥ 2 c^{-1/3}`, all `r`.

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- `V(y) = y^{5/2} Ψ(y)`. -/
noncomputable def uctV (y : ℂ) : ℂ := y ^ 2 * (y ^ (1 / 2 : ℂ) * uctG1Ext y)

lemma differentiableOn_uctV : DifferentiableOn ℂ uctV Complex.slitPlane := by
  intro w hw
  have hs := (hasDerivAt_cpow_half hw).differentiableAt
  have hΨ := (hasDerivAt_uctG1Ext hw).differentiableAt
  unfold uctV
  exact ((differentiableAt_pow 2).mul (hs.mul hΨ)).differentiableWithinAt

lemma uctV_sector : ∃ K : ℝ, 0 < K ∧ ∀ z : ℂ, InSector z → 5 ≤ ‖z‖ → ‖uctV z‖ ≤ K * ‖z‖ ^ (-(2 : ℝ)) := by
  obtain ⟨K, hK, h⟩ := uctG1Ext_sector
  refine ⟨K, hK, fun z hs hz5 => ?_⟩
  have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz5; simp at hz5; linarith
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have e : uctV z = z ^ (5 / 2 : ℂ) * uctG1Ext z := by unfold uctV; rw [cpow_five_half]; ring
  rw [e, norm_mul, norm_cpow_five_half hz0]
  calc ‖z‖ ^ (5 / 2 : ℝ) * ‖uctG1Ext z‖ ≤ ‖z‖ ^ (5 / 2 : ℝ) * (K * ‖z‖ ^ (-(9 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (h z hs hz5) (by positivity)
    _ = K * ‖z‖ ^ (-(2 : ℝ)) := by
        rw [mul_left_comm, ← Real.rpow_add hpos]; norm_num

theorem uctV_iteratedDeriv_bound (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 0 ≤ w.re → 2 ≤ ‖w‖ → ‖iteratedDeriv r uctV w‖ ≤ C * ‖w‖ ^ (-((2 : ℝ) + r)) := by
  obtain ⟨K, hK, h⟩ := uctV_sector
  exact deriv_bound_halfplane differentiableOn_uctV hK.le (by norm_num) (p := 2) h r

lemma slit_mul_real {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : w ∈ Complex.slitPlane) : ((t : ℂ) * w) ∈ Complex.slitPlane := by
  rcases hw with h | h
  · left; simp [Complex.mul_re]; positivity
  · right; simp [Complex.mul_im]; exact ⟨ht.ne', h⟩

/-- Scaling of derivatives by a positive real factor, for a function holomorphic on the slit plane. -/
lemma iteratedDeriv_comp_mul_real {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F Complex.slitPlane) {t : ℝ} (ht : 0 < t) (r : ℕ)
    {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    iteratedDeriv r (fun u : ℂ => F ((t : ℂ) * u)) w = (t : ℂ) ^ r * iteratedDeriv r F ((t : ℂ) * w) := by
  have hcd : ContDiffOn ℂ ⊤ F Complex.slitPlane := hF.contDiffOn Complex.isOpen_slitPlane
  have hmaps : Set.MapsTo (fun x : ℂ => (t : ℂ) * x) Complex.slitPlane Complex.slitPlane := fun x hx => slit_mul_real ht hx
  have h := iteratedDerivWithin_comp_const_smul (n := r) (x := w) (s := Complex.slitPlane) (f := F) (h := Complex.isOpen_slitPlane.uniqueDiffOn) (hx := hw) (hcd.of_le le_top) (t : ℂ) hmaps
  rw [iteratedDerivWithin_of_isOpen Complex.isOpen_slitPlane hw, iteratedDerivWithin_of_isOpen Complex.isOpen_slitPlane (hmaps hw)] at h
  simpa using h


/-- `C_Ai = -2^{5/3} / (√π c_s^{5/2})` (`§uct:sec2`). -/
noncomputable def uctCAi : ℝ := -(2 : ℝ) ^ (5 / 3 : ℝ) / (Real.sqrt π * ceCs ^ (5 / 2 : ℝ))

lemma uctCAi_mul : uctCAi * ceCs ^ (5 / 2 : ℝ) = -(2 * ceK / Real.sqrt π) := by
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hc : 0 < ceCs ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos ceCs_pos _
  have h2 : 2 * ceK = (2 : ℝ) ^ (5 / 3 : ℝ) := by
    unfold ceK
    rw [show (5 / 3 : ℝ) = 1 + 2 / 3 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
  unfold uctCAi
  rw [h2]; field_simp

lemma uctCAi_ne : uctCAi ≠ 0 := by
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hc : 0 < ceCs ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos ceCs_pos _
  unfold uctCAi
  have : 0 < (2 : ℝ) ^ (5 / 3 : ℝ) := by positivity
  exact div_ne_zero (neg_ne_zero.mpr this.ne') (by positivity)

lemma uctC_ne : uctC ≠ 0 := by
  unfold uctC
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have : (ceK : ℂ) ≠ 0 := by exact_mod_cast ceK_pos.ne'
  exact div_ne_zero this hs

/-- `φ_{c,δ}(w) = c^{5/6} C_Ai^{-1} w^{5/2} F̃_{*,δ}(i c_s c^{1/3} w)` (`(uct:phicd-bnds)`). -/
noncomputable def uctPhi (c δ : ℝ) (w : ℂ) : ℂ :=
  ((c ^ (5 / 6 : ℝ) / uctCAi : ℝ) : ℂ) * w ^ (5 / 2 : ℂ) *
    airyTwistedLaplaceC (uctFstarDelta δ) (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * w)

lemma cpow_ofReal_mul_five_half {b : ℝ} (hb : 0 < b) (w : ℂ) :
    ((b : ℂ) * w) ^ (5 / 2 : ℂ) = ((b ^ (5 / 2 : ℝ) : ℝ) : ℂ) * w ^ (5 / 2 : ℂ) := by
  rw [mul_comm, cpow_mul_ofReal_pos w hb, mul_comm]
  congr 1
  rw [Complex.ofReal_cpow hb.le]; push_cast; rfl

/-- On `Re w ≥ 0`, `φ_{c,δ}(w) - 1 = (2c_*)^{-1} (Z₁ + δ V)(c_s c^{1/3} w)` with `c_* = k/√π`. -/
lemma uctPhi_sub_one {c δ : ℝ} (hc : 0 < c) {w : ℂ} (hw : 0 ≤ w.re) :
    uctPhi c δ w - 1 = (1 / (2 * uctC)) * (uctZ1 (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * w) +
      (δ : ℂ) * uctV (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * w)) := by
  set b : ℝ := ceCs * c ^ (1 / 3 : ℝ) with hb
  have hb0 : 0 < b := by have := ceCs_pos; positivity
  set y : ℂ := (b : ℂ) * w with hy
  have hyre : 0 ≤ y.re := by rw [hy]; simp [Complex.mul_re]; positivity
  have hbp : b ^ (5 / 2 : ℝ) = ceCs ^ (5 / 2 : ℝ) * c ^ (5 / 6 : ℝ) := by
    rw [hb, Real.mul_rpow ceCs_pos.le (by positivity), ← Real.rpow_mul hc.le]; norm_num
  have hy52 : y ^ (5 / 2 : ℂ) = ((b ^ (5 / 2 : ℝ) : ℝ) : ℂ) * w ^ (5 / 2 : ℂ) := cpow_ofReal_mul_five_half hb0 w
  have hA : ((c ^ (5 / 6 : ℝ) / uctCAi : ℝ) : ℂ) * w ^ (5 / 2 : ℂ) = -(1 / (2 * uctC)) * y ^ (5 / 2 : ℂ) := by
    rw [hy52, hbp]
    have h1 := uctCAi_mul
    have h2 : (2 * uctC : ℂ) = ((2 * ceK / Real.sqrt π : ℝ) : ℂ) := by unfold uctC; push_cast; ring
    rw [h2]
    have hP : 0 < ceCs ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos ceCs_pos _
    have hK0 : 0 < 2 * ceK / Real.sqrt π := div_pos (by have := ceK_pos; positivity) (Real.sqrt_pos.mpr Real.pi_pos)
    have hC : uctCAi = -(2 * ceK / Real.sqrt π) / ceCs ^ (5 / 2 : ℝ) := by
      rw [eq_div_iff hP.ne']; exact h1
    have hreal : c ^ (5 / 6 : ℝ) / uctCAi = -(1 / (2 * ceK / Real.sqrt π)) * (ceCs ^ (5 / 2 : ℝ) * c ^ (5 / 6 : ℝ)) := by
      rw [hC]; field_simp
    rw [hreal]; push_cast; ring
  have hZ : y ^ (5 / 2 : ℂ) * uctF1Ext y = uctZ1 y + 2 * uctC := by
    unfold uctZ1; rw [cpow_five_half]; ring
  have hV : y ^ (5 / 2 : ℂ) * uctG1Ext y = uctV y := by
    unfold uctV; rw [cpow_five_half]; ring
  have hF : airyTwistedLaplaceC (uctFstarDelta δ) y = -uctF1Ext y - (δ : ℂ) * uctG1Ext y := airyTwistedLaplaceC_uctFstarDelta δ hyre
  have hc0 : (2 * uctC : ℂ) ≠ 0 := mul_ne_zero two_ne_zero uctC_ne
  unfold uctPhi
  rw [hA, hF]
  calc -(1 / (2 * uctC)) * y ^ (5 / 2 : ℂ) * (-uctF1Ext y - (δ : ℂ) * uctG1Ext y) - 1
      = (1 / (2 * uctC)) * (y ^ (5 / 2 : ℂ) * uctF1Ext y + (δ : ℂ) * (y ^ (5 / 2 : ℂ) * uctG1Ext y)) - 1 := by ring
    _ = (1 / (2 * uctC)) * (uctZ1 y + 2 * uctC + (δ : ℂ) * uctV y) - 1 := by rw [hZ, hV]
    _ = _ := by
        have hu := uctC_ne
        field_simp
        ring


lemma uniqueDiffOn_halfplane : UniqueDiffOn ℂ {w : ℂ | 0 ≤ w.re} := by
  refine UniqueDiffOn.of_real (uniqueDiffOn_convex (convex_halfSpace_re_ge 0) ?_)
  refine ⟨1, mem_interior.mpr ⟨{w : ℂ | 0 < w.re}, fun w (hw : 0 < w.re) => hw.le, isOpen_lt continuous_const Complex.continuous_re, by simp⟩⟩

lemma iteratedDerivWithin_halfplane_eq {h H : ℂ → ℂ} (hH : DifferentiableOn ℂ H Complex.slitPlane)
    (heq : ∀ w : ℂ, 0 ≤ w.re → h w = H w) {w : ℂ} (hw : 0 ≤ w.re) (hws : w ∈ Complex.slitPlane) (r : ℕ) :
    iteratedDerivWithin r h {w : ℂ | 0 ≤ w.re} w = iteratedDeriv r H w := by
  have hcd : ContDiffAt ℂ r H w := by
    have : ContDiffOn ℂ ⊤ H Complex.slitPlane := hH.contDiffOn Complex.isOpen_slitPlane
    exact (this.contDiffAt (Complex.isOpen_slitPlane.mem_nhds hws)).of_le (by exact_mod_cast le_top)
  rw [← iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_halfplane hcd hw]
  exact iteratedDerivWithin_congr (fun x hx => heq x hx) hw

lemma contDiffAt_of_slit {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F Complex.slitPlane) {w : ℂ} (hw : w ∈ Complex.slitPlane) (r : ℕ) :
    ContDiffAt ℂ r F w := by
  have : ContDiffOn ℂ ⊤ F Complex.slitPlane := hF.contDiffOn Complex.isOpen_slitPlane
  exact (this.contDiffAt (Complex.isOpen_slitPlane.mem_nhds hw)).of_le (by exact_mod_cast le_top)

lemma ceCs_gt_one : 1 < ceCs := by
  unfold ceCs
  apply Real.one_lt_rpow _ (by norm_num)
  have := Real.pi_gt_three
  nlinarith

lemma slit_of_ne {w : ℂ} (hw : 0 ≤ w.re) (h0 : w ≠ 0) : w ∈ Complex.slitPlane := by
  rcases hw.lt_or_eq with h | h
  · left; exact h
  · right; intro him; apply h0; apply Complex.ext <;> simp [← h, him]

/-- **`(uct:phicd-bnds)` of `uct:airy-trans` (2)**: derivative bounds for `φ_{c,δ} - 1` on the half plane, all orders `r`. -/
theorem uct_airy_trans_phi (r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ c δ : ℝ, 0 < c → 0 ≤ δ → δ ≤ 1 → ∀ w : ℂ, 0 ≤ w.re →
    2 * c ^ (-(1 / 3 : ℝ)) ≤ ‖w‖ →
      ‖iteratedDerivWithin r (fun w : ℂ => uctPhi c δ w - 1) {w : ℂ | 0 ≤ w.re} w‖ ≤ C * c ^ (-(2 / 3 : ℝ)) * ‖w‖ ^ (-((2 : ℝ) + r)) := by
  obtain ⟨C1, hC1, h1⟩ := uctZ1_iteratedDeriv_bound r
  obtain ⟨C2, hC2, h2⟩ := uctV_iteratedDeriv_bound r
  have hcs := ceCs_pos
  have hcs1 : 1 < ceCs := ceCs_gt_one
  have hu := uctC_ne
  have hcn : 0 < ‖uctC‖ := norm_pos_iff.mpr hu
  refine ⟨(1 / (2 * ‖uctC‖)) * ceCs ^ (-(2 : ℝ)) * (C1 + C2), by positivity, fun c δ hc hδ0 hδ1 w hw hwn => ?_⟩
  set b : ℝ := ceCs * c ^ (1 / 3 : ℝ) with hb
  have hc13 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have hb0 : 0 < b := by positivity
  have hcc : c ^ (1 / 3 : ℝ) * (2 * c ^ (-(1 / 3 : ℝ))) = 2 := by
    rw [mul_left_comm, ← Real.rpow_add hc]; norm_num
  have hbw : 2 ≤ b * ‖w‖ := by
    calc (2 : ℝ) = 1 * 2 := by ring
      _ ≤ ceCs * 2 := by nlinarith
      _ = ceCs * (c ^ (1 / 3 : ℝ) * (2 * c ^ (-(1 / 3 : ℝ)))) := by rw [hcc]
      _ ≤ ceCs * (c ^ (1 / 3 : ℝ) * ‖w‖) := by gcongr
      _ = b * ‖w‖ := by rw [hb]; ring
  have hw0 : w ≠ 0 := fun h0 => by rw [h0] at hbw; simp at hbw; linarith
  have hwn0 : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hwslit : w ∈ Complex.slitPlane := slit_of_ne hw hw0
  set G : ℂ → ℂ := fun y => (1 / (2 * uctC)) * (uctZ1 y + (δ : ℂ) * uctV y) with hG
  have hGd : DifferentiableOn ℂ G Complex.slitPlane := by
    have : DifferentiableOn ℂ (fun y => uctZ1 y + (δ : ℂ) * uctV y) Complex.slitPlane :=
      differentiableOn_uctZ1.add (differentiableOn_uctV.const_mul _)
    exact this.const_mul _
  set H : ℂ → ℂ := fun w' => G ((b : ℂ) * w') with hH
  have hHd : DifferentiableOn ℂ H Complex.slitPlane := by
    refine hGd.comp (differentiableOn_id.const_mul _) (fun x hx => slit_mul_real hb0 hx)
  have heq : ∀ w' : ℂ, 0 ≤ w'.re → uctPhi c δ w' - 1 = H w' := fun w' hw' => uctPhi_sub_one hc hw'
  rw [iteratedDerivWithin_halfplane_eq hHd heq hw hwslit r, hH, iteratedDeriv_comp_mul_real hGd hb0 r hwslit]
  have hys : (b : ℂ) * w ∈ Complex.slitPlane := slit_mul_real hb0 hwslit
  have hZd := contDiffAt_of_slit differentiableOn_uctZ1 hys r
  have hVd := contDiffAt_of_slit differentiableOn_uctV hys r
  have hGe : iteratedDeriv r G ((b : ℂ) * w) = (1 / (2 * uctC)) * (iteratedDeriv r uctZ1 ((b : ℂ) * w) + (δ : ℂ) * iteratedDeriv r uctV ((b : ℂ) * w)) := by
    have hVm : ContDiffAt ℂ r (fun x => (δ : ℂ) * uctV x) ((b : ℂ) * w) := contDiffAt_const.mul hVd
    have hSum : ContDiffAt ℂ r (fun x => uctZ1 x + (δ : ℂ) * uctV x) ((b : ℂ) * w) := hZd.add hVm
    rw [hG, iteratedDeriv_const_mul _ hSum, iteratedDeriv_fun_add hZd hVm, iteratedDeriv_const_mul _ hVd]
  rw [hGe, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]
  have hZb := h1 ((b : ℂ) * w) (by simp [Complex.mul_re]; positivity) (by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]; exact hbw)
  have hVb := h2 ((b : ℂ) * w) (by simp [Complex.mul_re]; positivity) (by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]; exact hbw)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0] at hZb hVb
  have hk : ‖(1 / (2 * uctC) : ℂ)‖ = 1 / (2 * ‖uctC‖) := by
    rw [norm_div, norm_one, norm_mul]; simp
  have hsum : ‖iteratedDeriv r uctZ1 ((b : ℂ) * w) + (δ : ℂ) * iteratedDeriv r uctV ((b : ℂ) * w)‖ ≤
      (C1 + C2) * (b * ‖w‖) ^ (-((2 : ℝ) + r)) := by
    calc _ ≤ ‖iteratedDeriv r uctZ1 ((b : ℂ) * w)‖ + ‖(δ : ℂ) * iteratedDeriv r uctV ((b : ℂ) * w)‖ := norm_add_le _ _
      _ ≤ C1 * (b * ‖w‖) ^ (-((2 : ℝ) + r)) + 1 * (C2 * (b * ‖w‖) ^ (-((2 : ℝ) + r))) := by
          apply add_le_add hZb
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ0]
          exact mul_le_mul hδ1 hVb (norm_nonneg _) zero_le_one
      _ = _ := by ring
  have hpow : b ^ r * (b * ‖w‖) ^ (-((2 : ℝ) + r)) = ceCs ^ (-(2 : ℝ)) * c ^ (-(2 / 3 : ℝ)) * ‖w‖ ^ (-((2 : ℝ) + r)) := by
    rw [Real.mul_rpow hb0.le hwn0.le, ← mul_assoc, ← Real.rpow_natCast b r, ← Real.rpow_add hb0,
      show (r : ℝ) + -((2 : ℝ) + r) = -2 by ring, hb, Real.mul_rpow hcs.le hc13.le, ← Real.rpow_mul hc.le]
    norm_num
  calc b ^ r * ‖(1 / (2 * uctC) : ℂ) * (iteratedDeriv r uctZ1 ((b : ℂ) * w) + (δ : ℂ) * iteratedDeriv r uctV ((b : ℂ) * w))‖
      = b ^ r * (‖(1 / (2 * uctC) : ℂ)‖ * ‖iteratedDeriv r uctZ1 ((b : ℂ) * w) + (δ : ℂ) * iteratedDeriv r uctV ((b : ℂ) * w)‖) := by rw [norm_mul]
    _ ≤ b ^ r * (1 / (2 * ‖uctC‖) * ((C1 + C2) * (b * ‖w‖) ^ (-((2 : ℝ) + r)))) := by
        rw [hk]; gcongr
    _ = (1 / (2 * ‖uctC‖)) * (C1 + C2) * (b ^ r * (b * ‖w‖) ^ (-((2 : ℝ) + r))) := by ring
    _ = _ := by rw [hpow]; ring


/-- Derivatives on the half plane of `w ↦ k F(t w)` for `F` holomorphic on the slit plane. -/
lemma iteratedDerivWithin_scaled {F h : ℂ → ℂ} (hF : DifferentiableOn ℂ F Complex.slitPlane) {t : ℝ} (ht : 0 < t) (k : ℂ)
    (heq : ∀ w : ℂ, 0 ≤ w.re → h w = k * F ((t : ℂ) * w)) {w : ℂ} (hw : 0 ≤ w.re) (hw0 : w ≠ 0) (r : ℕ) :
    iteratedDerivWithin r h {w : ℂ | 0 ≤ w.re} w = k * ((t : ℂ) ^ r * iteratedDeriv r F ((t : ℂ) * w)) := by
  have hws : w ∈ Complex.slitPlane := slit_of_ne hw hw0
  have hHd : DifferentiableOn ℂ (fun w' : ℂ => k * F ((t : ℂ) * w')) Complex.slitPlane :=
    (hF.comp (differentiableOn_id.const_mul _) (fun x hx => slit_mul_real ht hx)).const_mul k
  have hHd0 : DifferentiableOn ℂ (fun w' : ℂ => F ((t : ℂ) * w')) Complex.slitPlane :=
    hF.comp (differentiableOn_id.const_mul _) (fun x hx => slit_mul_real ht hx)
  rw [iteratedDerivWithin_halfplane_eq hHd heq hw hws r,
    iteratedDeriv_const_mul k (contDiffAt_of_slit hHd0 hws r), iteratedDeriv_comp_mul_real hF ht r hws]

/-- **`(uct:Fstar-asym)`, first estimate, of `uct:airy-trans` (2).**  `F_* = -f₁` (`uctFstarDelta 0`). -/
theorem uct_airy_trans_asymp_Fstar (r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 0 ≤ w.re → 2 ≤ ‖w‖ →
    ‖iteratedDerivWithin r (fun w : ℂ => w ^ (5 / 2 : ℂ) * airyTwistedLaplaceC (fun u => -ceF1 u) ((ceCs : ℂ) * w) - (uctCAi : ℂ))
      {w : ℂ | 0 ≤ w.re} w‖ ≤ C * ‖w‖ ^ (-((2 : ℝ) + r)) := by
  obtain ⟨C1, hC1, h1⟩ := uctZ1_iteratedDeriv_bound r
  have hcs := ceCs_pos
  have hcs1 := ceCs_gt_one
  have hu := uctC_ne
  set k : ℂ := (uctCAi : ℂ) / (2 * uctC) with hk
  have heq : ∀ w : ℂ, 0 ≤ w.re → (w ^ (5 / 2 : ℂ) * airyTwistedLaplaceC (fun u => -ceF1 u) ((ceCs : ℂ) * w) - (uctCAi : ℂ)) =
      k * uctZ1 ((ceCs : ℂ) * w) := by
    intro w hw
    have := uctPhi_sub_one (c := 1) (δ := 0) one_pos hw
    unfold uctPhi at this
    simp only [Real.one_rpow, mul_one, uctFstarDelta_zero] at this
    have hC := uctCAi_ne
    have hC' : (uctCAi : ℂ) ≠ 0 := by exact_mod_cast hC
    have e : ((1 / uctCAi : ℝ) : ℂ) = 1 / (uctCAi : ℂ) := by push_cast; ring
    rw [e] at this
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
    rw [hk]
    have hu2 : (2 * uctC : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hu
    calc w ^ (5 / 2 : ℂ) * airyTwistedLaplaceC (fun u => -ceF1 u) ((ceCs : ℂ) * w) - (uctCAi : ℂ)
        = (uctCAi : ℂ) * (1 / (uctCAi : ℂ) * w ^ (5 / 2 : ℂ) * airyTwistedLaplaceC (fun u => -ceF1 u) ((ceCs : ℂ) * w) - 1) := by
          field_simp
      _ = (uctCAi : ℂ) * (1 / (2 * uctC) * uctZ1 ((ceCs : ℂ) * w)) := by rw [this]
      _ = _ := by field_simp
  refine ⟨‖k‖ * ceCs ^ r * C1 * ceCs ^ (-((2 : ℝ) + r)), by positivity, fun w hw hwn => ?_⟩
  have hw0 : w ≠ 0 := fun h0 => by rw [h0] at hwn; simp at hwn; linarith
  rw [iteratedDerivWithin_scaled differentiableOn_uctZ1 hcs k heq hw hw0 r, norm_mul, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hcs]
  have hcw : ‖(ceCs : ℂ) * w‖ = ceCs * ‖w‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcs]
  have hb := h1 ((ceCs : ℂ) * w) (by simp [Complex.mul_re]; positivity) (by rw [hcw]; nlinarith)
  rw [hcw, Real.mul_rpow hcs.le (norm_nonneg _)] at hb
  calc ‖k‖ * (ceCs ^ r * ‖iteratedDeriv r uctZ1 ((ceCs : ℂ) * w)‖) ≤ ‖k‖ * (ceCs ^ r * (C1 * (ceCs ^ (-((2 : ℝ) + r)) * ‖w‖ ^ (-((2 : ℝ) + r))))) := by
        gcongr
    _ = _ := by ring

/-- **`(uct:Fstar-asym)`, second estimate, of `uct:airy-trans` (2).** -/
theorem uct_airy_trans_asymp_g1 (r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 0 ≤ w.re → 2 ≤ ‖w‖ →
    ‖iteratedDerivWithin r (fun w : ℂ => airyTwistedLaplaceC (ceG1 (airyZero 1)) ((ceCs : ℂ) * w)) {w : ℂ | 0 ≤ w.re} w‖ ≤
      C * ‖w‖ ^ (-((9 / 2 : ℝ) + r)) := by
  obtain ⟨C1, hC1, h1⟩ := uctG1Ext_iteratedDeriv_bound r
  have hcs := ceCs_pos
  have hcs1 := ceCs_gt_one
  have heq : ∀ w : ℂ, 0 ≤ w.re → airyTwistedLaplaceC (ceG1 (airyZero 1)) ((ceCs : ℂ) * w) = 1 * uctG1Ext ((ceCs : ℂ) * w) := by
    intro w hw
    rw [one_mul, uctG1Ext_eq (by simp [Complex.mul_re]; positivity)]
  refine ⟨ceCs ^ r * C1 * ceCs ^ (-((9 / 2 : ℝ) + r)), by positivity, fun w hw hwn => ?_⟩
  have hw0 : w ≠ 0 := fun h0 => by rw [h0] at hwn; simp at hwn; linarith
  rw [iteratedDerivWithin_scaled (F := uctG1Ext) differentiableOn_uctG1Ext hcs 1 heq hw hw0 r, one_mul, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcs]
  have hcw : ‖(ceCs : ℂ) * w‖ = ceCs * ‖w‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcs]
  have hb := h1 ((ceCs : ℂ) * w) (by simp [Complex.mul_re]; positivity) (by rw [hcw]; nlinarith)
  rw [hcw, Real.mul_rpow hcs.le (norm_nonneg _)] at hb
  calc ceCs ^ r * ‖iteratedDeriv r uctG1Ext ((ceCs : ℂ) * w)‖ ≤ ceCs ^ r * (C1 * (ceCs ^ (-((9 / 2 : ℝ) + r)) * ‖w‖ ^ (-((9 / 2 : ℝ) + r)))) := by
        gcongr
    _ = _ := by ring

end FormalResearch.SignUncertainty
