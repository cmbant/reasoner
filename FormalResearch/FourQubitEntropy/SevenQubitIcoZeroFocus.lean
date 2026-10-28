import FormalResearch.FourQubitEntropy.SevenQubitIcoPairSpectrum
import FormalResearch.FourQubitEntropy.SevenQubitConseqPurity

/-!
# Zero-focus covariants of the icosahedral family (`prop:zero-focus`, partial)

Source: `ResearchNotes/QI/seven_qubit_entanglement/sextic_covariant_generalizations.tex`,
`prop:zero-focus`.

**Definition used.** For a real seven-qubit vector `ψ` and `r ≤ 3` put
`V_r(ψ) = ∑_{|S|=r} (R_S ⊗ I_{Sᶜ}) ψ`, where `R_S` is the reduced matrix of `ψ` on `S` (`zfV`). The
paper's covariant `Φ_{∅,r}` is `(-1)^n V_r` (first assertion of the proposition). The defining
`L`/`M` contraction of `Φ_{∅,r}` with the spin-flipped tensor, and the identity
`Φ_{∅,r} = (-1)^n V_r`, are **not formalized**: `V_r` is taken as the definition of the covariant.

**Proved here, unconditionally** (for all real `alpha beta`, resp. on the family `α² = (1-2x)/30`,
`β² = x`):
* `zfV_inner_three`, `zfV_inner_two`, `zfV_inner_one`: `⟨ψ, V_r ψ⟩ = Q_r(ψ) = ∑_{|S|=r} tr ρ_S²`
  (the Euler identity `⟨z, V_r(z)⟩ = Q_r`);
* `zfV_hasDerivAt`: the directional derivative of `tr ρ_S²` at `ψ` in direction `φ` is `4⟨φ, V_S ψ⟩`
  (the real form of `∂Q_r/∂z̄ = 2 V_r`);
* `zeroFocus_one`: `V_1(ψ_x) = (7/2) V_0(ψ_x)`, i.e. the first relation of `eq:zero-focus-family`.

**Proved under an explicit hypothesis** (`PlaneHyp`, a `Prop` argument): that `V_r(ψ_x)` lies in the real
plane spanned by the two integer tables `alphaReal`, `betaReal` (`ψ_x = α·alphaReal + β·betaReal`).
This is the paper's "A₅ switching symmetry keeps `V_r(ψ_x)` in the real plane `span{ψ_x, ψ_x'}`", and is
**not proved here** (a computer check of it, by the eigenvector equations
`∑_{|S|=r}(P_S⊗I) alphaReal = p_r alphaReal`, etc., is not formalized). Under it:
* `zeroFocus_wronskian`: the second relation of `eq:zero-focus-family`,
  `4(104x-7) V_3 - 2(524x-37) V_2 + (96x²+3628x-263) V_0 = 0` (using only the exact purity coefficients
  of the pair and triple cuts, so the constants are derived, not assumed);
* `zeroFocus_three_ico`: at `x = 37/524`, `V_3 = (605/131) V_0`.
-/

open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-! ### The covariants -/

/-- Reduced Gram entry `∑_r ψ(a,r) ψ(b,r)` of a real vector across a cut. -/
def entryG {k l : ℕ} (c : Cut k l) (ψ : BitString → ℝ) (a b : Fin k → Bool) : ℝ :=
  ∑ r : Fin l → Bool, ψ (encode c a r) * ψ (encode c b r)

/-- `(R_S ⊗ I) ψ` evaluated at `z`, `S` the `k`-side of the cut `c`: for the unique `(a, r)` with
`encode c a r = z` it is `∑_b R(a,b) ψ(b, r)`. (For a bijective cut exactly one term is nonzero.) -/
def redApply {k l : ℕ} (c : Cut k l) (ψ : BitString → ℝ) (z : BitString) : ℝ :=
  ∑ a : Fin k → Bool, ∑ r : Fin l → Bool,
    if encode c a r = z then ∑ b, entryG c ψ a b * ψ (encode c b r) else 0

/-- The single-site masks. -/
def oneMasks : Finset (Fin 7 → Bool) := Finset.univ.filter fun m => weight m = 1

theorem oneMasks_card : oneMasks.card = 7 := by decide +kernel

theorem maskCut_bijective_one :
    ∀ m : Fin 7 → Bool, weight m = 1 → Function.Bijective (maskCut 1 6 m) := by
  decide +kernel

/-- `V_r(ψ) = ∑_{|S|=r} (R_S ⊗ I) ψ` for `r ≤ 3` (`V_0(ψ) = ‖ψ‖² ψ`; `V_r = 0` for `r > 3`, not used). -/
noncomputable def zfV (r : ℕ) (ψ : BitString → ℝ) (z : BitString) : ℝ :=
  match r with
  | 0 => (∑ w, ψ w ^ 2) * ψ z
  | 1 => ∑ m ∈ oneMasks, redApply (maskCut 1 6 m) ψ z
  | 2 => ∑ m ∈ pairMasks, redApply (maskCut 2 5 m) ψ z
  | 3 => ∑ m ∈ tripleMasks, redApply (maskCut 3 4 m) ψ z
  | _ => 0

theorem entry_eq_entryG {k l : ℕ} (c : Cut k l) (alpha beta : ℝ) (a b : Fin k → Bool) :
    entry c alpha beta a b = entryG c (icosahedralState alpha beta) a b := rfl

/-! ### Euler identity and gradient -/

theorem sum_mul_redApply {k l : ℕ} (c : Cut k l) (ψ φ : BitString → ℝ) :
    ∑ z, φ z * redApply c ψ z =
      ∑ a : Fin k → Bool, ∑ r : Fin l → Bool,
        φ (encode c a r) * ∑ b, entryG c ψ a b * ψ (encode c b r) := by
  unfold redApply
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [Finset.sum_ite_eq]

theorem entryG_symm {k l : ℕ} (c : Cut k l) (ψ : BitString → ℝ) (a b : Fin k → Bool) :
    entryG c ψ a b = entryG c ψ b a := by
  unfold entryG
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _

/-- `⟨φ, (R_S⊗I) ψ⟩ = ∑_{a,b} R_{ab} ∑_r φ(a,r) ψ(b,r)`. -/
theorem inner_redApply {k l : ℕ} (c : Cut k l) (ψ φ : BitString → ℝ) :
    ∑ z, φ z * redApply c ψ z =
      ∑ a : Fin k → Bool, ∑ b : Fin k → Bool,
        entryG c ψ a b * ∑ r : Fin l → Bool, φ (encode c a r) * ψ (encode c b r) := by
  rw [sum_mul_redApply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- `⟨ψ, (R_S⊗I) ψ⟩ = tr ρ_S²`. -/
theorem inner_self_redApply {k l : ℕ} (c : Cut k l) (ψ : BitString → ℝ) :
    ∑ z, ψ z * redApply c ψ z = ∑ a, ∑ b, entryG c ψ a b ^ 2 := by
  rw [inner_redApply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [pow_two]
  rfl

theorem inner_self_redApply_ico {k l : ℕ} (c : Cut k l) (alpha beta : ℝ) :
    ∑ z, icosahedralState alpha beta z * redApply c (icosahedralState alpha beta) z =
      purity c alpha beta :=
  inner_self_redApply c _

/-- Euler identity for `r = 3`: `⟨ψ, V_3 ψ⟩ = Q_3(ψ) = ∑_{|S|=3} tr ρ_S²`. -/
theorem zfV_inner_three (alpha beta : ℝ) :
    ∑ z, icosahedralState alpha beta z * zfV 3 (icosahedralState alpha beta) z =
      ∑ m ∈ tripleMasks, purity (maskCut 3 4 m) alpha beta := by
  simp only [zfV, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => inner_self_redApply_ico _ _ _

/-- Euler identity for `r = 2`: `⟨ψ, V_2 ψ⟩ = Q_2(ψ)`. -/
theorem zfV_inner_two (alpha beta : ℝ) :
    ∑ z, icosahedralState alpha beta z * zfV 2 (icosahedralState alpha beta) z =
      ∑ m ∈ pairMasks, purity (maskCut 2 5 m) alpha beta := by
  simp only [zfV, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => inner_self_redApply_ico _ _ _

/-- Euler identity for `r = 1`: `⟨ψ, V_1 ψ⟩ = Q_1(ψ) = ∑_i tr ρ_i²`. -/
theorem zfV_inner_one (alpha beta : ℝ) :
    ∑ z, icosahedralState alpha beta z * zfV 1 (icosahedralState alpha beta) z =
      ∑ m ∈ oneMasks, purity (maskCut 1 6 m) alpha beta := by
  simp only [zfV, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => inner_self_redApply_ico _ _ _

/-! ### Gradient: `d/dt tr ρ_S²(ψ + tφ) |_{t=0} = 4 ⟨φ, V_S ψ⟩` -/

theorem hasDerivAt_purity_dir {k l : ℕ} (c : Cut k l) (ψ φ : BitString → ℝ) :
    HasDerivAt (fun t : ℝ => ∑ a, ∑ b, entryG c (fun z => ψ z + t * φ z) a b ^ 2)
      (4 * ∑ z, φ z * redApply c ψ z) 0 := by
  set F : (Fin k → Bool) → (Fin k → Bool) → ℝ := fun a b => ∑ r, φ (encode c a r) * ψ (encode c b r)
    with hF
  set G : (Fin k → Bool) → (Fin k → Bool) → ℝ := fun a b => ∑ r, φ (encode c a r) * φ (encode c b r)
    with hG
  have hexp : ∀ (t : ℝ) a b, entryG c (fun z => ψ z + t * φ z) a b =
      entryG c ψ a b + t * (F a b + F b a) + t ^ 2 * G a b := by
    intro t a b
    simp only [entryG, hF, hG, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  simp only [hexp]
  have hd : ∀ a b, HasDerivAt (fun t : ℝ =>
      (entryG c ψ a b + t * (F a b + F b a) + t ^ 2 * G a b) ^ 2)
      (2 * entryG c ψ a b * (F a b + F b a)) 0 := by
    intro a b
    have h1 : HasDerivAt (fun t : ℝ => entryG c ψ a b + t * (F a b + F b a) + t ^ 2 * G a b)
        (F a b + F b a) 0 := by
      have h0 := ((hasDerivAt_id (0 : ℝ)).mul_const (F a b + F b a)).const_add (entryG c ψ a b)
      have h2 := (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (G a b))
      have h3 := h0.add h2
      convert h3 using 1
      · funext t; simp
      · simp
    have h4 := h1.pow 2
    convert h4 using 1
    simp [mul_assoc]
  have hs := HasDerivAt.sum (u := (Finset.univ : Finset (Fin k → Bool))) (fun a _ =>
    HasDerivAt.sum (u := (Finset.univ : Finset (Fin k → Bool))) (fun b _ => hd a b))
  convert hs using 1
  · ext t; simp
  · rw [inner_redApply]
    have e : ∀ a b, entryG c ψ a b * ∑ r, φ (encode c a r) * ψ (encode c b r) = entryG c ψ a b * F a b := by
      intros; rfl
    simp only [e, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    have e2 : ∑ a : Fin k → Bool, ∑ b : Fin k → Bool, entryG c ψ a b * F b a =
        ∑ a : Fin k → Bool, ∑ b : Fin k → Bool, entryG c ψ a b * F a b := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [entryG_symm]
    have e3 : ∀ a b, 2 * entryG c ψ a b * F b a = 2 * (entryG c ψ a b * F b a) := fun a b => by ring
    have e4 : ∀ a b, 2 * entryG c ψ a b * F a b = 2 * (entryG c ψ a b * F a b) := fun a b => by ring
    simp only [e3, e4, ← Finset.mul_sum, e2]
    ring

/-! ### The first relation: `Φ_{∅,1} = (7/2) Φ_{∅,0}` -/

/-- Every one-qubit cut has Gram matrices `Q = 0`, `P = 15·1`, `R = 1`. -/
theorem one_cuts_cert : ∀ m : Fin 7 → Bool, weight m = 1 → ∀ a b : Fin 1 → Bool,
    gramQ (maskCut 1 6 m) a b = 0 ∧ gramP (maskCut 1 6 m) a b = (if a = b then 15 else 0) ∧
      gramR (maskCut 1 6 m) a b = (if a = b then 1 else 0) := by
  decide +kernel

theorem entryG_one_cut (x alpha beta : ℝ) (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x)
    (m : Fin 7 → Bool) (hm : weight m = 1) (a b : Fin 1 → Bool) :
    entryG (maskCut 1 6 m) (icosahedralState alpha beta) a b = if a = b then 1 / 2 else 0 := by
  obtain ⟨hQ, hP, hR⟩ := one_cuts_cert m hm a b
  rw [← entry_eq_entryG, entry_expand, hQ, hP, hR]
  have h := coefficient_norm_identity x
  by_cases hab : a = b
  · simp only [hab, ↓reduceIte]
    push_cast
    rw [hα, hβ]
    linarith
  · simp [hab]

/-- For a bijective cut whose reduced matrix is `I/2`, `(R_S ⊗ I) ψ = ψ/2`. -/
theorem redApply_of_half {k l : ℕ} (c : Cut k l) (hc : Function.Bijective c) (ψ : BitString → ℝ)
    (h : ∀ a b, entryG c ψ a b = if a = b then 1 / 2 else 0) (z : BitString) :
    redApply c ψ z = ψ z / 2 := by
  have hf := FormalResearch.FourQubitEntropy.SevenQubitConseq.encode_bijective c hc
  have h1 : ∀ a r, (∑ b, entryG c ψ a b * ψ (encode c b r)) = ψ (encode c a r) / 2 := by
    intro a r
    simp [h, ite_mul, Finset.sum_ite_eq]
    ring
  unfold redApply
  simp only [h1]
  have h2 : ∑ a : Fin k → Bool, ∑ r : Fin l → Bool,
      (if encode c a r = z then ψ (encode c a r) / 2 else 0) =
      ∑ p : (Fin k → Bool) × (Fin l → Bool),
        (fun w : BitString => if w = z then ψ w / 2 else 0) (encode c p.1 p.2) := by
    rw [Fintype.sum_prod_type]
  rw [h2, hf.sum_comp (fun w : BitString => if w = z then ψ w / 2 else 0)]
  simp

theorem zfV_one_eq (x alpha beta : ℝ) (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x) (z : BitString) :
    zfV 1 (icosahedralState alpha beta) z = 7 / 2 * icosahedralState alpha beta z := by
  simp only [zfV]
  have : ∀ m ∈ oneMasks, redApply (maskCut 1 6 m) (icosahedralState alpha beta) z =
      icosahedralState alpha beta z / 2 := fun m hm =>
    redApply_of_half _ (maskCut_bijective_one m (Finset.mem_filter.1 hm).2) _
      (entryG_one_cut x alpha beta hα hβ m (Finset.mem_filter.1 hm).2) z
  rw [Finset.sum_congr rfl this, Finset.sum_const, oneMasks_card]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- `V_0(ψ_x) = ψ_x` (unit norm). -/
theorem zfV_zero_eq (x alpha beta : ℝ) (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x) (z : BitString) :
    zfV 0 (icosahedralState alpha beta) z = icosahedralState alpha beta z := by
  simp only [zfV]
  rw [icosahedralState_unit_norm x alpha beta hα hβ, one_mul]

/-- **`prop:zero-focus`, first relation of `eq:zero-focus-family`.**
`Φ_{∅,1}(ψ_x) = (7/2) Φ_{∅,0}(ψ_x)` (as `V_1 = (7/2) V_0`; `Φ_{∅,r} = (-1)^n V_r`). -/
theorem zeroFocus_one (x alpha beta : ℝ) (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x) (z : BitString) :
    zfV 1 (icosahedralState alpha beta) z = 7 / 2 * zfV 0 (icosahedralState alpha beta) z := by
  rw [zfV_one_eq x alpha beta hα hβ, zfV_zero_eq x alpha beta hα hβ]

/-! ### Inner products of `V_S ψ` with the two integer tables -/

/-- The real tables `alphaReal`, `betaReal` span the plane of `ψ_x`: `ψ = α·alphaReal + β·betaReal`. -/
theorem icosahedralState_eq (alpha beta : ℝ) (z : BitString) :
    icosahedralState alpha beta z = alpha * alphaReal z + beta * betaReal z := rfl

theorem alphaReal_sq : ∑ z, alphaReal z ^ 2 = 30 := by
  have h := alpha_coefficient_norm
  unfold alphaReal
  exact_mod_cast h

theorem betaReal_sq : ∑ z, betaReal z ^ 2 = 2 := by
  have h := beta_coefficient_norm
  unfold betaReal
  exact_mod_cast h

theorem alphaReal_betaReal : ∑ z, alphaReal z * betaReal z = 0 := by
  have h := coefficient_cross_term
  unfold alphaReal betaReal
  exact_mod_cast h

theorem gram_antisymm {k l : ℕ} (c : Cut k l) (hQ : ∀ a b, gramQ c a b = 0) (a b : Fin k → Bool) :
    gram c alphaCoefficient betaCoefficient a b = - gram c alphaCoefficient betaCoefficient b a := by
  have h := hQ a b
  unfold gramQ at h
  have e : gram c betaCoefficient alphaCoefficient a b = gram c alphaCoefficient betaCoefficient b a := by
    unfold gram
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  rw [e] at h
  linarith

theorem sum_symm_antisymm {ι : Type*} [Fintype ι] (f g : ι → ι → ℤ) (hf : ∀ a b, f a b = f b a)
    (hg : ∀ a b, g a b = - g b a) : ∑ a, ∑ b, f a b * g a b = 0 := by
  have h : ∑ a, ∑ b, f a b * g a b = - ∑ a, ∑ b, f a b * g a b := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hf b a, hg b a]
    ring
  linarith

theorem gramP_symm {k l : ℕ} (c : Cut k l) (a b : Fin k → Bool) : gramP c a b = gramP c b a :=
  gram_symm c alphaCoefficient a b

theorem gramR_symm {k l : ℕ} (c : Cut k l) (a b : Fin k → Bool) : gramR c a b = gramR c b a :=
  gram_symm c betaCoefficient a b

theorem purityCoeffs_c22_of_Q {k l : ℕ} (c : Cut k l) (hQ : ∀ a b, gramQ c a b = 0) :
    (purityCoeffs c).c22 = 2 * ∑ a, ∑ b, gramP c a b * gramR c a b := by
  simp only [purityCoeffs, hQ, zero_pow two_ne_zero, zero_add]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

/-- For a cut with `Q = 0`:
`⟨alphaReal, (R_S⊗I) ψ_x⟩ = α(α² ∑P² + β² ∑PR)` and
`⟨betaReal, (R_S⊗I) ψ_x⟩ = β(α² ∑PR + β² ∑R²)`, with `P, R` the integer Gram matrices. -/
theorem inner_alphaReal_redApply {k l : ℕ} (c : Cut k l) (hQ : ∀ a b, gramQ c a b = 0)
    (alpha beta : ℝ) :
    ∑ z, alphaReal z * redApply c (icosahedralState alpha beta) z =
      alpha * (alpha ^ 2 * (purityCoeffs c).c40 + beta ^ 2 * ((purityCoeffs c).c22 / 2)) := by
  have hA := sum_symm_antisymm (gramP c) (gram c alphaCoefficient betaCoefficient)
    (gramP_symm c) (gram_antisymm c hQ)
  have hB := sum_symm_antisymm (gramR c) (gram c alphaCoefficient betaCoefficient)
    (gramR_symm c) (gram_antisymm c hQ)
  have hA' : ∑ a, ∑ b, (gramP c a b : ℝ) * (gram c alphaCoefficient betaCoefficient a b : ℝ) = 0 := by
    exact_mod_cast hA
  have hB' : ∑ a, ∑ b, (gramR c a b : ℝ) * (gram c alphaCoefficient betaCoefficient a b : ℝ) = 0 := by
    exact_mod_cast hB
  have hc22 := purityCoeffs_c22_of_Q c hQ
  rw [inner_redApply]
  have e1 : ∀ a b, entryG c (icosahedralState alpha beta) a b =
      alpha ^ 2 * gramP c a b + beta ^ 2 * gramR c a b := by
    intro a b
    rw [← entry_eq_entryG, entry_expand, hQ]
    simp
  have e2 : ∀ a b, ∑ r : Fin l → Bool, alphaReal (encode c a r) *
      icosahedralState alpha beta (encode c b r) =
      alpha * gramP c a b + beta * gram c alphaCoefficient betaCoefficient a b := by
    intro a b
    simp only [icosahedralState_eq, gramP, gram, alphaReal, betaReal]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  simp only [e1, e2]
  have e3 : ∀ a b, (alpha ^ 2 * (gramP c a b : ℝ) + beta ^ 2 * (gramR c a b : ℝ)) *
      (alpha * gramP c a b + beta * (gram c alphaCoefficient betaCoefficient a b : ℝ)) =
      alpha ^ 3 * ((gramP c a b : ℝ) * gramP c a b) + alpha * beta ^ 2 * ((gramP c a b : ℝ) * gramR c a b) +
      alpha ^ 2 * beta * ((gramP c a b : ℝ) * (gram c alphaCoefficient betaCoefficient a b : ℝ)) +
      beta ^ 3 * ((gramR c a b : ℝ) * (gram c alphaCoefficient betaCoefficient a b : ℝ)) := by
    intros; ring
  simp only [e3, Finset.sum_add_distrib, ← Finset.mul_sum, hA', hB']
  have e40 : ∑ a, ∑ b, (gramP c a b : ℝ) * gramP c a b = ((purityCoeffs c).c40 : ℝ) := by
    simp only [purityCoeffs, pow_two]; push_cast; rfl
  have e22 : ∑ a, ∑ b, (gramP c a b : ℝ) * gramR c a b = ((purityCoeffs c).c22 : ℝ) / 2 := by
    rw [hc22]; push_cast; ring
  rw [e40, e22]
  ring

theorem gram_swap {k l : ℕ} (c : Cut k l) (a b : Fin k → Bool) :
    gram c betaCoefficient alphaCoefficient a b = gram c alphaCoefficient betaCoefficient b a := by
  unfold gram
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _

theorem gram_antisymm' {k l : ℕ} (c : Cut k l) (hQ : ∀ a b, gramQ c a b = 0) (a b : Fin k → Bool) :
    gram c betaCoefficient alphaCoefficient a b = - gram c betaCoefficient alphaCoefficient b a := by
  rw [gram_swap, gram_swap, gram_antisymm c hQ b a]

theorem inner_betaReal_redApply {k l : ℕ} (c : Cut k l) (hQ : ∀ a b, gramQ c a b = 0)
    (alpha beta : ℝ) :
    ∑ z, betaReal z * redApply c (icosahedralState alpha beta) z =
      beta * (alpha ^ 2 * ((purityCoeffs c).c22 / 2) + beta ^ 2 * (purityCoeffs c).c04) := by
  have hA := sum_symm_antisymm (gramP c) (gram c betaCoefficient alphaCoefficient)
    (gramP_symm c) (gram_antisymm' c hQ)
  have hB := sum_symm_antisymm (gramR c) (gram c betaCoefficient alphaCoefficient)
    (gramR_symm c) (gram_antisymm' c hQ)
  have hA' : ∑ a, ∑ b, (gramP c a b : ℝ) * (gram c betaCoefficient alphaCoefficient a b : ℝ) = 0 := by
    exact_mod_cast hA
  have hB' : ∑ a, ∑ b, (gramR c a b : ℝ) * (gram c betaCoefficient alphaCoefficient a b : ℝ) = 0 := by
    exact_mod_cast hB
  have hc22 := purityCoeffs_c22_of_Q c hQ
  rw [inner_redApply]
  have e1 : ∀ a b, entryG c (icosahedralState alpha beta) a b =
      alpha ^ 2 * gramP c a b + beta ^ 2 * gramR c a b := by
    intro a b
    rw [← entry_eq_entryG, entry_expand, hQ]
    simp
  have e2 : ∀ a b, ∑ r : Fin l → Bool, betaReal (encode c a r) *
      icosahedralState alpha beta (encode c b r) =
      alpha * gram c betaCoefficient alphaCoefficient a b + beta * gramR c a b := by
    intro a b
    simp only [icosahedralState_eq, gramR, gram, alphaReal, betaReal]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  simp only [e1, e2]
  have e3 : ∀ a b, (alpha ^ 2 * (gramP c a b : ℝ) + beta ^ 2 * (gramR c a b : ℝ)) *
      (alpha * (gram c betaCoefficient alphaCoefficient a b : ℝ) + beta * gramR c a b) =
      alpha ^ 3 * ((gramP c a b : ℝ) * (gram c betaCoefficient alphaCoefficient a b : ℝ)) +
      alpha ^ 2 * beta * ((gramP c a b : ℝ) * gramR c a b) +
      alpha * beta ^ 2 * ((gramR c a b : ℝ) * (gram c betaCoefficient alphaCoefficient a b : ℝ)) +
      beta ^ 3 * ((gramR c a b : ℝ) * gramR c a b) := by
    intros; ring
  simp only [e3, Finset.sum_add_distrib, ← Finset.mul_sum, hA', hB']
  have e04 : ∑ a, ∑ b, (gramR c a b : ℝ) * gramR c a b = ((purityCoeffs c).c04 : ℝ) := by
    simp only [purityCoeffs, pow_two]; push_cast; rfl
  have e22 : ∑ a, ∑ b, (gramP c a b : ℝ) * gramR c a b = ((purityCoeffs c).c22 : ℝ) / 2 := by
    rw [hc22]; push_cast; ring
  rw [e04, e22]
  ring

/-! ### Summing over the masks -/

theorem sum_pairMasks (F : (Fin 7 → Bool) → ℝ) (A B : ℝ)
    (h : ∀ m ∈ pairMasks, F m = if m 0 = true then A else B) :
    ∑ m ∈ pairMasks, F m = 6 * A + 15 * B := by
  rw [Finset.sum_congr rfl h, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    pairMasks_containing_card, pairMasks_avoiding_card]
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem sum_tripleMasks (F : (Fin 7 → Bool) → ℝ) (A B : ℝ)
    (h : ∀ m ∈ tripleMasks, F m = if m 0 = true then A else B) :
    ∑ m ∈ tripleMasks, F m = 15 * A + 20 * B := by
  rw [Finset.sum_congr rfl h, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    tripleMasks_containing_card, tripleMasks_avoiding_card]
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem tripleCut_Q (m : Fin 7 → Bool) (hm : weight m = 3) (a b : Triple) :
    gramQ (maskCut 3 4 m) a b = 0 := by
  have h := cuts_cert m hm
  by_cases h0 : m 0 = true
  · exact congrFun (congrFun (h.1 h0).1 a) b
  · exact congrFun (congrFun (h.2 h0).1 a) b

theorem pairCut_Q (m : Fin 7 → Bool) (hm : weight m = 2) (a b : Pair) :
    gramQ (maskCut 2 5 m) a b = 0 := by
  have h := pair_cuts_cert m hm
  by_cases h0 : m 0 = true
  · exact ((h.1 h0) a b).1
  · exact ((h.2 h0) a b).1

theorem alpha_inner_zfV_three (alpha beta : ℝ) :
    ∑ z, alphaReal z * zfV 3 (icosahedralState alpha beta) z =
      alpha * (4470 * alpha ^ 2 + 150 * beta ^ 2) := by
  simp only [zfV, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [sum_tripleMasks _ (alpha * (alpha ^ 2 * 146 + beta ^ 2 * 2)) (alpha * (alpha ^ 2 * 114 + beta ^ 2 * 6))]
  · ring
  · intro m hm
    have hm' := (Finset.mem_filter.1 hm).2
    rw [inner_alphaReal_redApply _ (tripleCut_Q m hm') alpha beta, triple_coeffs m hm']
    by_cases h0 : m 0 = true <;> simp [h0] <;> norm_num

theorem beta_inner_zfV_three (alpha beta : ℝ) :
    ∑ z, betaReal z * zfV 3 (icosahedralState alpha beta) z =
      beta * (150 * alpha ^ 2 + 70 * beta ^ 2) := by
  simp only [zfV, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [sum_tripleMasks _ (beta * (alpha ^ 2 * 2 + beta ^ 2 * 2)) (beta * (alpha ^ 2 * 6 + beta ^ 2 * 2))]
  · ring
  · intro m hm
    have hm' := (Finset.mem_filter.1 hm).2
    rw [inner_betaReal_redApply _ (tripleCut_Q m hm') alpha beta, triple_coeffs m hm']
    by_cases h0 : m 0 = true <;> simp [h0] <;> norm_num

theorem alpha_inner_zfV_two (alpha beta : ℝ) :
    ∑ z, alphaReal z * zfV 2 (icosahedralState alpha beta) z =
      alpha * (4890 * alpha ^ 2 + 270 * beta ^ 2) := by
  simp only [zfV, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [sum_pairMasks _ (alpha * (alpha ^ 2 * 250 + beta ^ 2 * 10)) (alpha * (alpha ^ 2 * 226 + beta ^ 2 * 14))]
  · ring
  · intro m hm
    have hm' := (Finset.mem_filter.1 hm).2
    rw [inner_alphaReal_redApply _ (pairCut_Q m hm') alpha beta, pair_coeffs m hm']
    by_cases h0 : m 0 = true <;> simp [h0] <;> norm_num

theorem beta_inner_zfV_two (alpha beta : ℝ) :
    ∑ z, betaReal z * zfV 2 (icosahedralState alpha beta) z =
      beta * (270 * alpha ^ 2 + 42 * beta ^ 2) := by
  simp only [zfV, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [sum_pairMasks _ (beta * (alpha ^ 2 * 10 + beta ^ 2 * 2)) (beta * (alpha ^ 2 * 14 + beta ^ 2 * 2))]
  · ring
  · intro m hm
    have hm' := (Finset.mem_filter.1 hm).2
    rw [inner_betaReal_redApply _ (pairCut_Q m hm') alpha beta, pair_coeffs m hm']
    by_cases h0 : m 0 = true <;> simp [h0] <;> norm_num

/-! ### The second relation, under the plane hypothesis -/

/-- **Hypothesis (not proved here).** `V_r(ψ)` lies in the real plane spanned by the integer tables
`alphaReal`, `betaReal`, i.e. in `span{ψ_x, ψ_x'}`. This is the paper's consequence of the `A₅` switching
symmetry (`prop:zero-focus`, proof); for `r = 2, 3` it is equivalent to
`∑_{|S|=r} (P_S ⊗ I)` and `∑_{|S|=r} (R_S ⊗ I)` having `alphaReal`, `betaReal` as eigenvectors. -/
def PlaneHyp (r : ℕ) (alpha beta : ℝ) : Prop :=
  ∃ s t : ℝ, ∀ z, zfV r (icosahedralState alpha beta) z = s * alphaReal z + t * betaReal z

theorem plane_alpha_inner {r : ℕ} {alpha beta s t : ℝ}
    (h : ∀ z, zfV r (icosahedralState alpha beta) z = s * alphaReal z + t * betaReal z) :
    ∑ z, alphaReal z * zfV r (icosahedralState alpha beta) z = 30 * s := by
  have : ∀ z, alphaReal z * zfV r (icosahedralState alpha beta) z =
      s * alphaReal z ^ 2 + t * (alphaReal z * betaReal z) := fun z => by rw [h z]; ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, alphaReal_sq, alphaReal_betaReal]
  ring

theorem plane_beta_inner {r : ℕ} {alpha beta s t : ℝ}
    (h : ∀ z, zfV r (icosahedralState alpha beta) z = s * alphaReal z + t * betaReal z) :
    ∑ z, betaReal z * zfV r (icosahedralState alpha beta) z = 2 * t := by
  have : ∀ z, betaReal z * zfV r (icosahedralState alpha beta) z =
      s * (alphaReal z * betaReal z) + t * betaReal z ^ 2 := fun z => by rw [h z]; ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, betaReal_sq, alphaReal_betaReal]
  ring

/-- Under the plane hypothesis, `V_3(ψ) = α(149α²+5β²) alphaReal + β(75α²+35β²) betaReal`. -/
theorem zfV_three_of_plane (alpha beta : ℝ) (h : PlaneHyp 3 alpha beta) (z : BitString) :
    zfV 3 (icosahedralState alpha beta) z =
      alpha * (149 * alpha ^ 2 + 5 * beta ^ 2) * alphaReal z +
        beta * (75 * alpha ^ 2 + 35 * beta ^ 2) * betaReal z := by
  obtain ⟨s, t, hst⟩ := h
  have h1 := plane_alpha_inner hst
  have h2 := plane_beta_inner hst
  rw [alpha_inner_zfV_three] at h1
  rw [beta_inner_zfV_three] at h2
  rw [hst z]
  have hs : s = alpha * (149 * alpha ^ 2 + 5 * beta ^ 2) := by linarith
  have ht : t = beta * (75 * alpha ^ 2 + 35 * beta ^ 2) := by linarith
  rw [hs, ht]

/-- Under the plane hypothesis, `V_2(ψ) = α(163α²+9β²) alphaReal + β(135α²+21β²) betaReal`. -/
theorem zfV_two_of_plane (alpha beta : ℝ) (h : PlaneHyp 2 alpha beta) (z : BitString) :
    zfV 2 (icosahedralState alpha beta) z =
      alpha * (163 * alpha ^ 2 + 9 * beta ^ 2) * alphaReal z +
        beta * (135 * alpha ^ 2 + 21 * beta ^ 2) * betaReal z := by
  obtain ⟨s, t, hst⟩ := h
  have h1 := plane_alpha_inner hst
  have h2 := plane_beta_inner hst
  rw [alpha_inner_zfV_two] at h1
  rw [beta_inner_zfV_two] at h2
  rw [hst z]
  have hs : s = alpha * (163 * alpha ^ 2 + 9 * beta ^ 2) := by linarith
  have ht : t = beta * (135 * alpha ^ 2 + 21 * beta ^ 2) := by linarith
  rw [hs, ht]

/-- **`prop:zero-focus`, second relation of `eq:zero-focus-family`, under `PlaneHyp 2` and `PlaneHyp 3`.**
`4(104x-7) Φ_{∅,3} - 2(524x-37) Φ_{∅,2} + (96x²+3628x-263) Φ_{∅,0} = 0` along `ψ_x`
(stated for `V_r = (-1)^n Φ_{∅,r}`; the relation is homogeneous). -/
theorem zeroFocus_wronskian (x alpha beta : ℝ) (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x)
    (h2 : PlaneHyp 2 alpha beta) (h3 : PlaneHyp 3 alpha beta) (z : BitString) :
    4 * (104 * x - 7) * zfV 3 (icosahedralState alpha beta) z -
        2 * (524 * x - 37) * zfV 2 (icosahedralState alpha beta) z +
        (96 * x ^ 2 + 3628 * x - 263) * zfV 0 (icosahedralState alpha beta) z = 0 := by
  rw [zfV_three_of_plane alpha beta h3, zfV_two_of_plane alpha beta h2, zfV_zero_eq x alpha beta hα hβ,
    icosahedralState_eq]
  have hu : alpha ^ 2 = (1 - 2 * x) / 30 := hα
  have e1 : 4 * (104 * x - 7) * (149 * alpha ^ 2 + 5 * beta ^ 2) -
      2 * (524 * x - 37) * (163 * alpha ^ 2 + 9 * beta ^ 2) + (96 * x ^ 2 + 3628 * x - 263) = 0 := by
    rw [hu, hβ]; ring
  have e2 : 4 * (104 * x - 7) * (75 * alpha ^ 2 + 35 * beta ^ 2) -
      2 * (524 * x - 37) * (135 * alpha ^ 2 + 21 * beta ^ 2) + (96 * x ^ 2 + 3628 * x - 263) = 0 := by
    rw [hu, hβ]; ring
  linear_combination (alpha * alphaReal z) * e1 + (beta * betaReal z) * e2

/-- At `x = 37/524` and under `PlaneHyp 3`: `Φ_{∅,3}(Ψ_ico) = (605/131) Φ_{∅,0}(Ψ_ico)`. -/
theorem zeroFocus_three_ico (alpha beta : ℝ) (hα : alpha ^ 2 = u (37 / 524)) (hβ : beta ^ 2 = 37 / 524)
    (h3 : PlaneHyp 3 alpha beta) (z : BitString) :
    zfV 3 (icosahedralState alpha beta) z = 605 / 131 * zfV 0 (icosahedralState alpha beta) z := by
  rw [zfV_three_of_plane alpha beta h3, zfV_zero_eq (37 / 524) alpha beta hα hβ, icosahedralState_eq]
  have hu : alpha ^ 2 = 15 / 524 := by rw [hα]; unfold u; norm_num
  rw [hu, hβ]
  ring

end FormalResearch.FourQubitEntropy.SevenQubitIco

