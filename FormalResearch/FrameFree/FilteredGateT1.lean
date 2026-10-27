import FormalResearch.FrameFree.FilteredGateConj
import FormalResearch.FrameFree.FilteredGateRot
import FormalResearch.FrameFree.FilteredGateReal
import FormalResearch.FrameFree.FilteredGateBiv


/-!
# Filtered-gate law: the Bloch block of the gauge unitary

For `T = U† (φ ⊗ φ n̂) U` the Bloch block `h_{ab} = ¼ tr[(σ_a⊗1) T (σ_b⊗1) T†]` equals the cofactor
matrix of `Q = C ρ C + S ρ' S` (`hh_formula`), with `ρ = rot φ`, `ρ' = rot (φ n̂)`.  Hence for
`sin 4c_k ≥ 0` the pair bound `q_T(X₁) + q_T(X₂) ≤ 2 + 2 δ` holds (`pair_le`).
-/

open scoped Matrix Kronecker ComplexConjugate
open Finset Complex

namespace FormalResearch.FrameFree.FTG

theorem trace_kr4 (p q r s φ ψ : M2) :
    (kr p q * kr φ ψ * kr r s * (kr φ ψ)ᴴ).trace =
      (p * φ * r * φᴴ).trace * (q * ψ * s * ψᴴ).trace := by
  rw [kr_conjTranspose, kr_mul, kr_mul, kr_mul, kr_trace]

theorem tr_sig_rb (φ : M2) (p r : Fin 4) :
    (sig p * φ * sig r * φᴴ).trace = 2 * rb φ p r := by
  unfold rb; ring

theorem hh_T (c : Fin 3 → ℝ) (Φ : M4) (a b : Fin 3) :
    hh ((Ug c)ᴴ * Φ * Ug c) a.succ b.succ =
      (1 / 4) * (Ug c * kr (sig a.succ) 1 * (Ug c)ᴴ * Φ *
        (Ug c * kr (sig b.succ) 1 * (Ug c)ᴴ) * Φᴴ).trace := by
  unfold hh
  congr 1
  have : kr (sig a.succ) 1 * ((Ug c)ᴴ * Φ * Ug c) * kr (sig b.succ) 1 *
      ((Ug c)ᴴ * Φ * Ug c)ᴴ =
      (kr (sig a.succ) 1 * (Ug c)ᴴ * Φ * Ug c * kr (sig b.succ) 1 * (Ug c)ᴴ * Φᴴ) * Ug c := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem T_unitary (c : Fin 3 → ℝ) (Φ : M4) (h : Φ * Φᴴ = 1) :
    ((Ug c)ᴴ * Φ * Ug c) * ((Ug c)ᴴ * Φ * Ug c)ᴴ = 1 := by
  have e : ((Ug c)ᴴ * Φ * Ug c) * ((Ug c)ᴴ * Φ * Ug c)ᴴ =
      (Ug c)ᴴ * Φ * (Ug c * (Ug c)ᴴ) * Φᴴ * Ug c := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, Ug_mul_conjT, Matrix.mul_one, Matrix.mul_assoc _ Φ, h, Matrix.mul_one]
  exact Ug_conjT_mul c

theorem kr_unitary (φ ψ : M2) (hφ : φ * φᴴ = 1) (hψ : ψ * ψᴴ = 1) :
    kr φ ψ * (kr φ ψ)ᴴ = 1 := by
  rw [kr_conjTranspose, kr_mul, hφ, hψ, kr_one]

/-- The cosine / sine vectors `C_k = cos 2c_k`, `S_k = sin 2c_k`. -/
noncomputable def Cv (c : Fin 3 → ℝ) : V3 := fun k => Real.cos (2 * c k)
noncomputable def Sv (c : Fin 3 → ℝ) : V3 := fun k => Real.sin (2 * c k)

theorem hh_formula (c : Fin 3 → ℝ) (φ ψ : M2) (hφ : φ * φᴴ = 1) (hφ' : φᴴ * φ = 1)
    (hψ : ψ * ψᴴ = 1) (hψ' : ψᴴ * ψ = 1) (a b : Fin 3) :
    hh ((Ug c)ᴴ * kr φ ψ * Ug c) a.succ b.succ =
      ((cofm (Qm (Cv c) (Sv c) (rot φ) (rot ψ)) a b : ℝ) : ℂ) := by
  have hρ := rot_cof φ hφ' a b
  have hρ' := rot_cof ψ hψ' a b
  unfold cofm at hρ hρ'
  have hρC : (rot φ (a + 1) (b + 1) : ℂ) * rot φ (a + 2) (b + 2) -
      rot φ (a + 1) (b + 2) * rot φ (a + 2) (b + 1) = rot φ a b := by exact_mod_cast hρ
  have hρC' : (rot ψ (a + 1) (b + 1) : ℂ) * rot ψ (a + 2) (b + 2) -
      rot ψ (a + 1) (b + 2) * rot ψ (a + 2) (b + 1) = rot ψ a b := by exact_mod_cast hρ'
  rw [hh_T, A_conj, A_conj]
  simp only [← sig_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, trace_kr4, tr_sig_rb,
    rb_succ_eq, rb_00 _ hφ, rb_00 _ hψ, rb_0s _ hφ', rb_0s _ hψ', rb_s0 _ hφ, rb_s0 _ hψ]
  unfold cofm Qm Cv Sv
  push_cast
  simp only [smul_eq_mul]
  linear_combination
    -(Complex.cos (2 * (c (a + 1) : ℂ)) * Complex.cos (2 * (c (a + 2) : ℂ)) *
      Complex.cos (2 * (c (b + 1) : ℂ)) * Complex.cos (2 * (c (b + 2) : ℂ))) * hρC +
    -(Complex.sin (2 * (c (a + 1) : ℂ)) * Complex.sin (2 * (c (a + 2) : ℂ)) *
      Complex.sin (2 * (c (b + 1) : ℂ)) * Complex.sin (2 * (c (b + 2) : ℂ))) * hρC'

theorem dl_nonneg (c : Fin 3 → ℝ) : 0 ≤ dl c := (abs_nonneg _).trans (le_dl c 0)

theorem dl_le_one (c : Fin 3 → ℝ) : dl c ≤ 1 := by
  unfold dl
  exact max_le (max_le (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)) (Real.abs_cos_le_one _)

/-- The unitary `Φ = φ ⊗ φ n̂`. -/
theorem Phi_unitary (φ : M2) (hφ : φ * φᴴ = 1) (n : V3) (hn : sq3 n = 1) :
    (φ * nh n) * (φ * nh n)ᴴ = 1 := by
  rw [Matrix.conjTranspose_mul, nh_herm, Matrix.mul_assoc, ← Matrix.mul_assoc (nh n), nh_sq n hn,
    Matrix.one_mul, hφ]

theorem Phi_unitary' (φ : M2) (hφ' : φᴴ * φ = 1) (n : V3) (hn : sq3 n = 1) :
    (φ * nh n)ᴴ * (φ * nh n) = 1 := by
  rw [Matrix.conjTranspose_mul, nh_herm, Matrix.mul_assoc, ← Matrix.mul_assoc φᴴ, hφ',
    Matrix.one_mul, nh_sq n hn]

/-- The gauge unitary `T = U† (φ ⊗ φ n̂) U`. -/
noncomputable def Tg (c : Fin 3 → ℝ) (φ : M2) (n : V3) : M4 :=
  (Ug c)ᴴ * kr φ (φ * nh n) * Ug c

theorem Tg_unitary (c : Fin 3 → ℝ) (φ : M2) (hφ : φ * φᴴ = 1) (n : V3) (hn : sq3 n = 1) :
    Tg c φ n * (Tg c φ n)ᴴ = 1 :=
  T_unitary c _ (kr_unitary _ _ hφ (Phi_unitary φ hφ n hn))

/-- **Pair bound for the gauge unitary** (good `c`: all `sin 4c_k ≥ 0`). -/
theorem pair_le (c : Fin 3 → ℝ) (hgood : ∀ k, 0 ≤ Real.sin (4 * c k)) (φ : M2)
    (hφ : φ * φᴴ = 1) (hφ' : φᴴ * φ = 1) (n : V3) (hn : sq3 n = 1)
    (X₁ X₂ : M2) (h11 : (X₁ * X₁ᴴ).trace = 1) (h22 : (X₂ * X₂ᴴ).trace = 1)
    (h12 : (X₁ * X₂ᴴ).trace = 0) (h21 : (X₂ * X₁ᴴ).trace = 0) :
    qf (rlg (Tg c φ n)) (fun i => X₁ i.1 i.2) + qf (rlg (Tg c φ n)) (fun i => X₂ i.1 i.2) ≤
      2 + 2 * dl c := by
  refine qf_pair_le (Tg c φ n) (Tg_unitary c φ hφ n hn)
    (cofm (Qm (Cv c) (Sv c) (rot φ) (rot (φ * nh n)))) (dl c) (dl_nonneg c) ?_ ?_
    X₁ X₂ h11 h22 h12 h21
  · intro x y hx hy
    refine tau_bound (Cv c) (Sv c) (fun i => ?_) (fun i => ?_) (dl c) (dl_le_one c) (fun i => ?_)
      (rot_orth φ hφ') n hn (rot_refl φ n hn) x y hx hy
    · simp only [Cv, Sv]; exact Real.cos_sq_add_sin_sq _
    · simp only [Cv, Sv]
      have := hgood i
      have e : Real.sin (4 * c i) = 2 * (Real.sin (2 * c i) * Real.cos (2 * c i)) := by
        rw [show 4 * c i = 2 * (2 * c i) by ring, Real.sin_two_mul]; ring
      nlinarith [e]
    · simp only [Cv, Sv]
      have e : Real.cos (2 * c i) ^ 2 - Real.sin (2 * c i) ^ 2 = Real.cos (4 * c i) := by
        rw [show 4 * c i = 2 * (2 * c i) by ring, Real.cos_two_mul' (2 * c i)]
      rw [e]; exact le_dl c i
  · intro a b
    exact hh_formula c φ (φ * nh n) hφ hφ' (Phi_unitary φ hφ n hn) (Phi_unitary' φ hφ' n hn) a b

end FormalResearch.FrameFree.FTG
