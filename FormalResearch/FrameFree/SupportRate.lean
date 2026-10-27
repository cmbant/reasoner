import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ComplexConjugate InnerProductSpace BigOperators

/-!
# Support rate, abstract part: tensor algebra (`thm:supportrate`, hard half)

Namespace `FormalResearch.FrameFree.SupportRate`.
-/

namespace FormalResearch.FrameFree.SupportRate

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The one-copy space `ℂ^N`. -/
abbrev V (N : Type*) [Fintype N] := EuclideanSpace ℂ N

/-- The `d`-fold tensor power space `(ℂ^N)^{⊗d}`. -/
abbrev Eg (N : Type*) [Fintype N] (d : ℕ) := EuclideanSpace ℂ (Fin d → N)

/-- `z^{⊗d}`. -/
def pw (z : V N) (d : ℕ) : Eg N d := WithLp.toLp 2 fun β => ∏ i, z (β i)

theorem sum_cons {M : Type*} [AddCommMonoid M] {k : ℕ} (F : (Fin (k + 1) → N) → M) :
    ∑ β, F β = ∑ j, ∑ γ : Fin k → N, F (Fin.cons j γ) := by
  rw [← (Fin.consEquiv (fun _ => N)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem inner_eg {d : ℕ} (u v : Eg N d) : ⟪u, v⟫_ℂ = ∑ β, conj (u β) * v β := by
  simp [PiLp.inner_apply, mul_comm]

theorem norm_sq_eg {d : ℕ} (u : Eg N d) : ‖u‖ ^ 2 = ∑ β, ‖u β‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]

/-- Prepending a vector: `u ↦ a ⊗ u`. -/
def Clin (a : V N) (d : ℕ) : Eg N d →ₗ[ℂ] Eg N (d + 1) where
  toFun u := WithLp.toLp 2 fun β => a (β 0) * u (Fin.tail β)
  map_add' u v := by ext β; simp [mul_add]
  map_smul' c u := by ext β; simp; ring

theorem Clin_apply (a : V N) (d : ℕ) (u : Eg N d) (β : Fin (d + 1) → N) :
    Clin a d u β = a (β 0) * u (Fin.tail β) := rfl

theorem norm_Clin (a : V N) (d : ℕ) (u : Eg N d) : ‖Clin a d u‖ = ‖a‖ * ‖u‖ := by
  have h : ‖Clin a d u‖ ^ 2 = (‖a‖ * ‖u‖) ^ 2 := by
    rw [norm_sq_eg, mul_pow, EuclideanSpace.norm_sq_eq a, norm_sq_eg u, Finset.sum_mul_sum, sum_cons]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun γ _ => ?_
    simp [Clin_apply, Fin.tail_cons, mul_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h

/-- Prepending a vector, as a continuous linear map. -/
noncomputable def Cc (a : V N) (d : ℕ) : Eg N d →L[ℂ] Eg N (d + 1) :=
  (Clin a d).mkContinuous ‖a‖ fun u => (norm_Clin a d u).le

theorem Cc_apply (a : V N) (d : ℕ) (u : Eg N d) : Cc a d u = Clin a d u := rfl

theorem norm_Cc_le (a : V N) (d : ℕ) : ‖Cc a d‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => (norm_Clin a d u).le

theorem Cc_add (a b : V N) (d : ℕ) : Cc (a + b) d = Cc a d + Cc b d := by
  ext u β; simp [Cc_apply, Clin_apply, add_mul]

theorem Cc_smul (c : ℂ) (a : V N) (d : ℕ) : Cc (c • a) d = c • Cc a d := by
  ext u β; simp [Cc_apply, Clin_apply, mul_assoc]

theorem Cc_zero (d : ℕ) : Cc (0 : V N) d = 0 := by
  ext u β; simp [Cc_apply, Clin_apply]

theorem inner_V (z a : V N) : ⟪z, a⟫_ℂ = ∑ j, conj (z j) * a j := by
  simp [PiLp.inner_apply, mul_comm]

/-- The slice of a tensor at first index `j`. -/
def slice {k : ℕ} (j : N) (r : Eg N (k + 1)) : Eg N k :=
  WithLp.toLp 2 fun γ => r (Fin.cons j γ)

theorem inner_pw_succ (z : V N) (k : ℕ) (r : Eg N (k + 1)) :
    ⟪pw z (k + 1), r⟫_ℂ = ∑ j, conj (z j) * ⟪pw z k, slice j r⟫_ℂ := by
  rw [inner_eg, sum_cons]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_eg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  simp [pw, slice, Fin.prod_univ_succ, mul_assoc]

/-- **Key identity.** `⟨z^{⊗(d+1)}, a ⊗ u⟩ = ⟨z,a⟩ ⟨z^{⊗d}, u⟩`. -/
theorem KL (z a : V N) (d : ℕ) (u : Eg N d) :
    ⟪pw z (d + 1), Cc a d u⟫_ℂ = ⟪z, a⟫_ℂ * ⟪pw z d, u⟫_ℂ := by
  rw [inner_eg, sum_cons, inner_V, inner_eg, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun γ _ => ?_
  simp [pw, Cc_apply, Clin_apply, Fin.prod_univ_succ, Fin.tail_cons]
  ring

/-- Basis vector. -/
noncomputable def ev (j : N) : V N := EuclideanSpace.single j 1

theorem inner_pw_zero (z : V N) (r : Eg N 0) : ⟪pw z 0, r⟫_ℂ = r (fun i => i.elim0) := by
  rw [inner_eg]
  simp [pw]
  congr 1

/-- `Σ_α r_α C_{α_1} ⋯ C_{α_k}`, i.e. `u ↦ r ⊗ u`. -/
noncomputable def Cr : (k : ℕ) → Eg N k → (m : ℕ) → Eg N m →L[ℂ] Eg N (m + k)
  | 0, r, m => (r (fun i => i.elim0)) • (ContinuousLinearMap.id ℂ (Eg N m))
  | k + 1, r, m => ∑ j, (Cc (ev j) (m + k)).comp (Cr k (slice j r) m)

theorem KLgen (z : V N) : ∀ (k : ℕ) (r : Eg N k) (m : ℕ) (u : Eg N m),
    ⟪pw z (m + k), Cr k r m u⟫_ℂ = ⟪pw z k, r⟫_ℂ * ⟪pw z m, u⟫_ℂ := by
  intro k
  induction k with
  | zero =>
    intro r m u
    simp only [Cr, smul_apply, ContinuousLinearMap.id_apply, inner_smul_right,
      inner_pw_zero]
    rfl
  | succ k ih =>
    intro r m u
    rw [inner_pw_succ, Finset.sum_mul]
    simp only [Cr, sum_apply, ContinuousLinearMap.comp_apply, inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (KL z (ev j) (m + k) (Cr k (slice j r) m u)).trans ?_
    rw [ih]
    simp [ev, inner_V]
    ring

/-- The span of the `d`-th tensor powers of the vectors of `O`. -/
def W (O : Set (V N)) (d : ℕ) : Submodule ℂ (Eg N d) :=
  Submodule.span ℂ ((fun z => pw z d) '' O)

theorem pw_mem_W {O : Set (V N)} {z : V N} (hz : z ∈ O) (d : ℕ) : pw z d ∈ W O d :=
  Submodule.subset_span ⟨z, hz, rfl⟩

theorem mem_Wperp {O : Set (V N)} {d : ℕ} {r : Eg N d} :
    r ∈ (W O d)ᗮ ↔ ∀ z ∈ O, ⟪pw z d, r⟫_ℂ = 0 := by
  rw [Submodule.mem_orthogonal]
  refine ⟨fun h z hz => h _ (pw_mem_W hz d), fun h w hw => ?_⟩
  induction hw using Submodule.span_induction with
  | mem w hw => obtain ⟨z, hz, rfl⟩ := hw; exact h z hz
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- `W^⊥` is an ideal: `a ⊗ W_d^⊥ ⊂ W_{d+1}^⊥`. -/
theorem Cc_mem_Wperp {O : Set (V N)} {d : ℕ} (a : V N) {y : Eg N d} (hy : y ∈ (W O d)ᗮ) :
    Cc a d y ∈ (W O (d + 1))ᗮ := by
  rw [mem_Wperp] at hy ⊢
  intro z hz
  rw [KL, hy z hz, mul_zero]

/-- `W^⊥` is an ideal: `r ⊗ u ∈ W_{m+k}^⊥` for `r ∈ W_k^⊥`. -/
theorem Cr_mem_Wperp {O : Set (V N)} {k : ℕ} {r : Eg N k} (hr : r ∈ (W O k)ᗮ) (m : ℕ)
    (u : Eg N m) : Cr k r m u ∈ (W O (m + k))ᗮ := by
  rw [mem_Wperp] at hr ⊢
  intro z hz
  rw [KLgen, hr z hz, zero_mul]

/-- Antisymmetry: `a ⊗ b ⊗ u - b ⊗ a ⊗ u ∈ W^⊥`. -/
theorem swap_mem_Wperp {O : Set (V N)} (a b : V N) {d : ℕ} (u : Eg N d) :
    Cc a (d + 1) (Cc b d u) - Cc b (d + 1) (Cc a d u) ∈ (W O (d + 2))ᗮ := by
  rw [mem_Wperp]
  intro z hz
  rw [inner_sub_right, KL, KL, KL, KL]
  ring

theorem starProjection_eq_of_sub_mem {O : Set (V N)} {d : ℕ} {η η' : Eg N d}
    (h : η - η' ∈ (W O d)ᗮ) : (W O d).starProjection η = (W O d).starProjection η' := by
  have := (Submodule.starProjection_apply_eq_zero_iff (K := W O d)).2 h
  rw [map_sub, sub_eq_zero] at this
  exact this


section Lift

variable {E : ℕ → Type*} [∀ d, NormedAddCommGroup (E d)] [∀ d, NormedSpace ℂ (E d)]

/-- Components of the forward shift of `ξ` by the maps `g d : E d → E (d+1)`. -/
def fwdFun (g : ∀ d, E d →L[ℂ] E (d + 1)) (ξ : ∀ d, E d) : ∀ d, E d
  | 0 => 0
  | d + 1 => g d (ξ d)

theorem fwdFun_memℓp (g : ∀ d, E d →L[ℂ] E (d + 1)) {C : ℝ} (hC : ∀ d, ‖g d‖ ≤ C)
    (ξ : lp E 2) : Memℓp (fwdFun g ξ) 2 := by
  have hs : Summable fun d => ‖ξ d‖ ^ (2 : ℝ) := by
    have := (lp.memℓp ξ).summable (by norm_num)
    simpa using this
  refine memℓp_gen ?_
  simp only [ENNReal.toReal_ofNat]
  refine (summable_nat_add_iff 1).1 ?_
  refine Summable.of_nonneg_of_le (fun d => by positivity) (fun d => ?_) (hs.mul_left (C ^ 2))
  have h1 : ‖g d (ξ d)‖ ≤ C * ‖ξ d‖ := (g d).le_of_opNorm_le (hC d) _
  have h0 : 0 ≤ ‖g d (ξ d)‖ := norm_nonneg _
  show ‖g d (ξ d)‖ ^ (2 : ℝ) ≤ C ^ 2 * ‖ξ d‖ ^ (2 : ℝ)
  rw [Real.rpow_two, Real.rpow_two, ← mul_pow]
  exact pow_le_pow_left₀ h0 h1 2

/-- Forward shift as an element of `lp`. -/
def fwdLp (g : ∀ d, E d →L[ℂ] E (d + 1)) {C : ℝ} (hC : ∀ d, ‖g d‖ ≤ C) (ξ : lp E 2) : lp E 2 :=
  ⟨fwdFun g ξ, fwdFun_memℓp g hC ξ⟩

theorem fwdLp_apply_zero (g : ∀ d, E d →L[ℂ] E (d + 1)) {C : ℝ} (hC : ∀ d, ‖g d‖ ≤ C) (ξ : lp E 2) :
    fwdLp g hC ξ 0 = 0 := rfl

theorem fwdLp_apply_succ (g : ∀ d, E d →L[ℂ] E (d + 1)) {C : ℝ} (hC : ∀ d, ‖g d‖ ≤ C) (ξ : lp E 2)
    (d : ℕ) : fwdLp g hC ξ (d + 1) = g d (ξ d) := rfl

theorem fwdLp_norm_le (g : ∀ d, E d →L[ℂ] E (d + 1)) {C : ℝ} (hC : ∀ d, ‖g d‖ ≤ C) (ξ : lp E 2) :
    ‖fwdLp g hC ξ‖ ≤ C * ‖ξ‖ := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hs : Summable fun d => ‖ξ d‖ ^ (2 : ℝ) := by
    have := (lp.memℓp ξ).summable (by norm_num)
    simpa using this
  have hn : ∑' d, ‖ξ d‖ ^ (2 : ℝ) = ‖ξ‖ ^ (2 : ℝ) := by
    have := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) ξ
    simpa using this.symm
  refine lp.norm_le_of_tsum_le (by norm_num) (mul_nonneg hC0 (norm_nonneg _)) ?_
  simp only [ENNReal.toReal_ofNat]
  have hsum : Summable fun i => ‖fwdLp g hC ξ i‖ ^ (2 : ℝ) := by
    have := (lp.memℓp (fwdLp g hC ξ)).summable (by norm_num)
    simpa using this
  have hs' := (summable_nat_add_iff 1).2 hsum
  rw [Summable.tsum_eq_zero_add hsum]
  rw [fwdLp_apply_zero]
  simp only [norm_zero, Real.zero_rpow two_ne_zero, zero_add]
  calc ∑' d, ‖fwdLp g hC ξ (d + 1)‖ ^ (2 : ℝ) ≤ ∑' d, C ^ 2 * ‖ξ d‖ ^ (2 : ℝ) := by
        refine Summable.tsum_le_tsum (fun d => ?_) hs' (hs.mul_left _)
        rw [fwdLp_apply_succ]
        have h1 : ‖g d (ξ d)‖ ≤ C * ‖ξ d‖ := (g d).le_of_opNorm_le (hC d) _
        rw [Real.rpow_two, Real.rpow_two, ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (C * ‖ξ‖) ^ (2 : ℝ) := by
        rw [tsum_mul_left, hn, Real.rpow_two, Real.rpow_two, mul_pow]

/-- The forward shift as a continuous linear map. -/
noncomputable def fwd (g : ∀ d, E d →L[ℂ] E (d + 1)) {C : ℝ} (hC : ∀ d, ‖g d‖ ≤ C) :
    lp E 2 →L[ℂ] lp E 2 :=
  LinearMap.mkContinuous
    { toFun := fwdLp g hC
      map_add' := fun ξ η => by
        ext d; cases d <;> simp [fwdLp_apply_zero, fwdLp_apply_succ]
      map_smul' := fun c ξ => by
        ext d; cases d <;> simp [fwdLp_apply_zero, fwdLp_apply_succ] }
    C (fwdLp_norm_le g hC)

theorem norm_fwd_le (g : ∀ d, E d →L[ℂ] E (d + 1)) {C : ℝ} (hC : ∀ d, ‖g d‖ ≤ C) :
    ‖fwd g hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ (le_trans (norm_nonneg _) (hC 0)) _

theorem fwd_apply_zero (g : ∀ d, E d →L[ℂ] E (d + 1)) {C : ℝ} (hC : ∀ d, ‖g d‖ ≤ C) (ξ : lp E 2) :
    fwd g hC ξ 0 = 0 := rfl

theorem fwd_apply_succ (g : ∀ d, E d →L[ℂ] E (d + 1)) {C : ℝ} (hC : ∀ d, ‖g d‖ ≤ C) (ξ : lp E 2)
    (d : ℕ) : fwd g hC ξ (d + 1) = g d (ξ d) := rfl

end Lift

instance instHOP (O : Set (V N)) (d : ℕ) : (W O d).HasOrthogonalProjection := inferInstance

section Operators

variable (O : Set (V N))

theorem Cc_pw (x : V N) (d : ℕ) : Cc x d (pw x d) = pw x (d + 1) := by
  ext β
  simp [Cc_apply, Clin_apply, pw, Fin.prod_univ_succ, Fin.tail]

theorem proj_Cc_proj (a : V N) (d : ℕ) (w : Eg N d) :
    (W O (d + 1)).starProjection (Cc a d ((W O d).starProjection w)) =
      (W O (d + 1)).starProjection (Cc a d w) := by
  apply starProjection_eq_of_sub_mem
  have h := Cc_mem_Wperp (O := O) a (Submodule.sub_starProjection_mem_orthogonal (K := W O d) w)
  have h2 := Submodule.neg_mem _ h
  convert h2 using 1
  simp [map_sub]

theorem proj_swap (a b : V N) (d : ℕ) (u : Eg N d) :
    (W O (d + 2)).starProjection (Cc a (d + 1) (Cc b d u)) =
      (W O (d + 2)).starProjection (Cc b (d + 1) (Cc a d u)) :=
  starProjection_eq_of_sub_mem (swap_mem_Wperp a b u)

/-- The compressed creation map `W_d → W_{d+1}`, `u ↦ P_{d+1} (a ⊗ u)`. -/
noncomputable def gmap (a : V N) (d : ℕ) : ↥(W O d) →L[ℂ] ↥(W O (d + 1)) :=
  (((W O (d + 1)).starProjection ∘L (Cc a d) ∘L (W O d).subtypeL)).codRestrict (W O (d + 1))
    (fun u => Submodule.starProjection_apply_mem _ _)

theorem gmap_coe (a : V N) (d : ℕ) (u : ↥(W O d)) :
    (gmap O a d u : Eg N (d + 1)) = (W O (d + 1)).starProjection (Cc a d (u : Eg N d)) := rfl

theorem norm_gmap_le (a : V N) (d : ℕ) : ‖gmap O a d‖ ≤ ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  have h1 : ‖(gmap O a d u : Eg N (d + 1))‖ ≤ ‖Cc a d (u : Eg N d)‖ := by
    rw [gmap_coe]; exact Submodule.norm_starProjection_apply_le _ _
  have h2 : ‖Cc a d (u : Eg N d)‖ ≤ ‖a‖ * ‖(u : Eg N d)‖ := (Cc a d).le_of_opNorm_le (norm_Cc_le a d) _
  calc ‖gmap O a d u‖ = ‖(gmap O a d u : Eg N (d + 1))‖ := rfl
    _ ≤ ‖a‖ * ‖u‖ := h1.trans h2

/-- The Hilbert space `⊕_d W_d` (as an `ℓ²` sum). -/
abbrev H : Type _ := lp (fun d : ℕ => ↥(W O d)) 2

/-- The compressed shift `T_a`. -/
noncomputable def T (a : V N) : H O →L[ℂ] H O := fwd (gmap O a) (fun d => norm_gmap_le O a d)

theorem T_zero (a : V N) (ξ : H O) : T O a ξ 0 = 0 := rfl

theorem T_succ (a : V N) (ξ : H O) (d : ℕ) : T O a ξ (d + 1) = gmap O a d (ξ d) := rfl

theorem norm_T_le (a : V N) : ‖T O a‖ ≤ ‖a‖ :=
  norm_fwd_le _ _

theorem Cc_sum (a : V N) (d : ℕ) : Cc a d = ∑ j, a j • Cc (ev j) d := by
  ext u β
  simp [Cc_apply, Clin_apply, ev, PiLp.single_apply]

theorem T_sum (a : V N) : T O a = ∑ j, a j • T O (ev j) := by
  refine ContinuousLinearMap.ext fun ξ => lp.ext (funext fun d => ?_)
  rw [sum_apply, lp.coeFn_sum]
  simp only [Finset.sum_apply, smul_apply, lp.coeFn_smul, Pi.smul_apply]
  cases d with
  | zero => simp [T_zero]
  | succ d =>
    apply Subtype.ext
    simp only [T_succ, Submodule.coe_sum, Submodule.coe_smul, gmap_coe]
    conv_lhs => rw [Cc_sum a d]
    simp [map_sum]

theorem T_comm (a b : V N) : T O a * T O b = T O b * T O a := by
  refine ContinuousLinearMap.ext fun ξ => lp.ext (funext fun d => ?_)
  show T O a (T O b ξ) d = T O b (T O a ξ) d
  rcases d with _ | _ | d
  · simp [T_zero]
  · simp [T_succ, T_zero]
  · apply Subtype.ext
    simp only [T_succ, gmap_coe]
    rw [proj_Cc_proj, proj_Cc_proj]
    exact proj_swap O a b d _

/-- `Θ_k(r) = Σ_α r_α T_{α_1} ⋯ T_{α_k}` (slice recursion). -/
noncomputable def Th : (k : ℕ) → Eg N k → (H O →L[ℂ] H O)
  | 0, r => (r (fun i => i.elim0)) • (1 : H O →L[ℂ] H O)
  | k + 1, r => ∑ j, T O (ev j) * Th k (slice j r)

theorem Th_apply_lt : ∀ (k : ℕ) (r : Eg N k) (ξ : H O) (d : ℕ), d < k → Th O k r ξ d = 0 := by
  intro k
  induction k with
  | zero => intro r ξ d hd; exact absurd hd (Nat.not_lt_zero _)
  | succ k ih =>
    intro r ξ d hd
    simp only [Th, sum_apply, ContinuousLinearMap.mul_apply]
    rw [lp.coeFn_sum]
    simp only [Finset.sum_apply]
    cases d with
    | zero => simp [T_zero]
    | succ d =>
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [T_succ, ih _ _ d (Nat.lt_of_succ_lt_succ hd), map_zero]

theorem Th_apply : ∀ (k : ℕ) (r : Eg N k) (ξ : H O) (m : ℕ),
    ((Th O k r ξ (m + k) : ↥(W O (m + k))) : Eg N (m + k)) =
      (W O (m + k)).starProjection (Cr k r m (ξ m : Eg N m)) := by
  intro k
  induction k with
  | zero =>
    intro r ξ m
    simp only [Th, Cr, smul_apply, ContinuousLinearMap.one_apply, lp.coeFn_smul, Pi.smul_apply, Submodule.coe_smul,
      map_smul]
    congr 1
    exact (Submodule.starProjection_eq_self_iff.2 (ξ m).2).symm
  | succ k ih =>
    intro r ξ m
    simp only [Th, Cr, sum_apply, ContinuousLinearMap.mul_apply]
    rw [lp.coeFn_sum]
    simp only [Finset.sum_apply, Submodule.coe_sum, map_sum, ContinuousLinearMap.comp_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    show ((gmap O (ev j) (m + k) (Th O k (slice j r) ξ (m + k)) : ↥(W O (m + k + 1))) : Eg N (m + k + 1)) = _
    rw [gmap_coe, ih, proj_Cc_proj]
    rfl

theorem Th_eq_zero {k : ℕ} {r : Eg N k} (hr : r ∈ (W O k)ᗮ) : Th O k r = 0 := by
  refine ContinuousLinearMap.ext fun ξ => lp.ext (funext fun d => ?_)
  by_cases hd : d < k
  · simp [Th_apply_lt O k r ξ d hd]
  · obtain ⟨m, rfl⟩ : ∃ m, d = m + k := ⟨d - k, by omega⟩
    apply Subtype.ext
    have h := (Submodule.starProjection_apply_eq_zero_iff (K := W O (m + k))).2 (Cr_mem_Wperp hr m (ξ m : Eg N m))
    simp [Th_apply, h]

theorem pw_zero_eq (x z : V N) : pw x 0 = pw z 0 := by
  ext β; simp [pw]

theorem norm_pw_zero (z : V N) : ‖pw z 0‖ = 1 := by
  have h : ‖pw z 0‖ ^ 2 = 1 := by
    rw [norm_sq_eg]; simp [pw]
  nlinarith [norm_nonneg (pw z 0)]

/-- The vacuum vector of `⊕ W_d`. -/
noncomputable def one {z0 : V N} (hz0 : z0 ∈ O) : H O :=
  lp.single 2 0 (⟨pw z0 0, pw_mem_W hz0 0⟩ : ↥(W O 0))

theorem norm_one {z0 : V N} (hz0 : z0 ∈ O) : ‖one O hz0‖ = 1 := by
  rw [one, lp.norm_single (by norm_num)]
  exact norm_pw_zero z0

theorem vac (x : V N) {z0 : V N} (hz0 : z0 ∈ O) : ∀ d : ℕ,
    (((((T O x) ^ d) (one O hz0)) d : ↥(W O d)) : Eg N d) =
      (W O d).starProjection (pw x d)
  | 0 => by
    simp only [pow_zero, ContinuousLinearMap.one_apply, one, lp.single_apply_self]
    rw [pw_zero_eq x z0]
    exact (Submodule.starProjection_eq_self_iff.2 (pw_mem_W hz0 0)).symm
  | d + 1 => by
    rw [pow_succ', ContinuousLinearMap.mul_apply, T_succ, gmap_coe, vac x hz0 d, proj_Cc_proj,
      Cc_pw]

theorem Rk_le_norm_pow (x : V N) {z0 : V N} (hz0 : z0 ∈ O) (d : ℕ) :
    ‖(W O d).starProjection (pw x d)‖ ≤ ‖(T O x) ^ d‖ := by
  rw [← vac O x hz0 d]
  calc ‖(((((T O x) ^ d) (one O hz0)) d : ↥(W O d)) : Eg N d)‖
      = ‖((((T O x) ^ d) (one O hz0)) d : ↥(W O d))‖ := rfl
    _ ≤ ‖(((T O x) ^ d) (one O hz0))‖ := lp.norm_apply_le_norm (by norm_num) _ _
    _ ≤ ‖(T O x) ^ d‖ * ‖one O hz0‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖(T O x) ^ d‖ := by rw [norm_one, mul_one]

end Operators

end FormalResearch.FrameFree.SupportRate
