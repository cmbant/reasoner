import FormalResearch.FrameFree.FilteredGateT1


/-!
# Filtered-gate law: the Kramers gauge for the spectator

For `W` unitary and any `C` there is a real unit `n` with `K = C n̂ ς Wᵀ` symmetric (`ς = σ_y`), and
`W ⊗ C = det W · (ς ⊗ K)(φ ⊗ φ n̂)` with `φ = W̄ ς` unitary (`kr_W_C`).  `tr_reduce` and
`fro2_reduce` move the unitary `Φ = φ ⊗ φ n̂` onto the overlap side, `T = U† Φ U`.
-/

open scoped Matrix Kronecker ComplexConjugate
open Finset Complex

namespace FormalResearch.FrameFree.FTG

theorem unit_entries (W : M2) (h : Wᴴ * W = 1) :
    conj (W 0 0) * W 0 0 + conj (W 1 0) * W 1 0 = 1 ∧
    conj (W 0 0) * W 0 1 + conj (W 1 0) * W 1 1 = 0 ∧
    conj (W 0 1) * W 0 0 + conj (W 1 1) * W 1 0 = 0 ∧
    conj (W 0 1) * W 0 1 + conj (W 1 1) * W 1 1 = 1 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def] at h00 h01 h10 h11
  exact ⟨h00, h01, h10, h11⟩

theorem unit_entries' (W : M2) (h : Wᴴ * W = 1) :
    W 0 0 * conj (W 0 0) + W 0 1 * conj (W 0 1) = 1 ∧
    W 0 0 * conj (W 1 0) + W 0 1 * conj (W 1 1) = 0 ∧
    W 1 0 * conj (W 0 0) + W 1 1 * conj (W 0 1) = 0 ∧
    W 1 0 * conj (W 1 0) + W 1 1 * conj (W 1 1) = 1 := by
  have h' : W * Wᴴ = 1 := mul_eq_one_comm.mp h
  have h00 := congrFun (congrFun h' 0) 0
  have h01 := congrFun (congrFun h' 0) 1
  have h10 := congrFun (congrFun h' 1) 0
  have h11 := congrFun (congrFun h' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def] at h00 h01 h10 h11
  exact ⟨h00, h01, h10, h11⟩

theorem W_det_rel (W : M2) (h : Wᴴ * W = 1) :
    W 0 0 = W.det * conj (W 1 1) ∧ W 0 1 = -(W.det * conj (W 1 0)) ∧
    W 1 0 = -(W.det * conj (W 0 1)) ∧ W 1 1 = W.det * conj (W 0 0) := by
  obtain ⟨u00, u01, u10, u11⟩ := unit_entries W h
  obtain ⟨v00, v01, v10, v11⟩ := unit_entries' W h
  rw [Matrix.det_fin_two]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- Entrywise complex conjugate. -/
noncomputable def Wb (W : M2) : M2 := W.map conj

theorem sig2_conj (M : M2) :
    (sig 2 * M * sig 2) 0 0 = M 1 1 ∧ (sig 2 * M * sig 2) 0 1 = -M 1 0 ∧
    (sig 2 * M * sig 2) 1 0 = -M 0 1 ∧ (sig 2 * M * sig 2) 1 1 = M 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [sig] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem W_eq (W : M2) (h : Wᴴ * W = 1) : W = W.det • (sig 2 * Wb W * sig 2) := by
  obtain ⟨r0, r1, r2, r3⟩ := W_det_rel W h
  obtain ⟨s0, s1, s2, s3⟩ := sig2_conj (Wb W)
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.smul_apply, smul_eq_mul, Fin.zero_eta,
    Fin.mk_one, s0, s1, s2, s3] <;> simp only [Wb, Matrix.map_apply]
  · exact r0
  · linear_combination r1
  · linear_combination r2
  · exact r3

theorem Wb_unit (W : M2) (h : Wᴴ * W = 1) :
    Wb W * (Wb W)ᴴ = 1 ∧ (Wb W)ᴴ * Wb W = 1 ∧ Wᵀ * Wb W = 1 := by
  obtain ⟨u00, u01, u10, u11⟩ := unit_entries W h
  obtain ⟨v00, v01, v10, v11⟩ := unit_entries' W h
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Wb, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def,
      Matrix.one_apply] <;> grind

theorem phi_unit (W : M2) (h : Wᴴ * W = 1) :
    (Wb W * sig 2) * (Wb W * sig 2)ᴴ = 1 ∧ (Wb W * sig 2)ᴴ * (Wb W * sig 2) = 1 := by
  obtain ⟨h1, h2, -⟩ := Wb_unit W h
  have hs : sig 2 * sig 2 = 1 := sig_sq 2
  have hh : (sig 2)ᴴ = sig 2 := sig_herm 2
  constructor
  · rw [Matrix.conjTranspose_mul, hh, Matrix.mul_assoc, ← Matrix.mul_assoc (sig 2), hs, Matrix.one_mul, h1]
  · rw [Matrix.conjTranspose_mul, hh, Matrix.mul_assoc, ← Matrix.mul_assoc (Wb W)ᴴ, h2, Matrix.one_mul, hs]

theorem kr_W_C (W C : M2) (h : Wᴴ * W = 1) (n : V3) (hn : sq3 n = 1) :
    kr W C = W.det • (kr (sig 2) (C * nh n * sig 2 * Wᵀ) * kr (Wb W * sig 2) ((Wb W * sig 2) * nh n)) := by
  obtain ⟨-, -, h3⟩ := Wb_unit W h
  have hs : sig 2 * sig 2 = 1 := sig_sq 2
  have hB : C * nh n * sig 2 * Wᵀ * ((Wb W * sig 2) * nh n) = C := by
    calc C * nh n * sig 2 * Wᵀ * ((Wb W * sig 2) * nh n)
        = C * nh n * sig 2 * (Wᵀ * Wb W) * sig 2 * nh n := by simp only [Matrix.mul_assoc]
      _ = C := by
        have e : C * nh n * sig 2 * (1 : M2) * sig 2 * nh n = C * (nh n * (sig 2 * sig 2) * nh n) := by
          simp only [Matrix.mul_assoc, Matrix.mul_one]
        rw [h3, e, hs, Matrix.mul_one, nh_sq n hn, Matrix.mul_one]
  rw [kr_mul, hB, ← Matrix.mul_assoc, ← kr_smul_left]
  congr 1
  exact W_eq W h

/-- A nonzero real solution of one complex linear equation in three real unknowns. -/
theorem exists_real_kernel (c₁ c₂ c₃ : ℂ) :
    ∃ p q r : ℝ, 0 < p ^ 2 + q ^ 2 + r ^ 2 ∧ (p : ℂ) * c₁ + q * c₂ + r * c₃ = 0 := by
  let f : (Fin 3 → ℝ) →ₗ[ℝ] ℂ :=
    { toFun := fun v => ((v 0 : ℝ) : ℂ) * c₁ + ((v 1 : ℝ) : ℂ) * c₂ + ((v 2 : ℝ) : ℂ) * c₃
      map_add' := by intro v w; simp only [Pi.add_apply, Complex.ofReal_add]; ring
      map_smul' := by intro a v; simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
        RingHom.id_apply, Complex.real_smul]; ring }
  have hk : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp [Complex.finrank_real_complex])
  obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  refine ⟨v 0, v 1, v 2, ?_, hv⟩
  by_contra hcon
  apply hne
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  funext i; fin_cases i <;> simpa

theorem exists_unit_gauge (C W : M2) :
    ∃ n : V3, sq3 n = 1 ∧
      (C * nh n * sig 2 * Wᵀ) 0 1 = (C * nh n * sig 2 * Wᵀ) 1 0 := by
  set E : Fin 3 → M2 := fun l => C * sig l.succ * sig 2 * Wᵀ with hE
  obtain ⟨p, q, r, hs, h⟩ := exists_real_kernel (E 0 0 1 - E 0 1 0) (E 1 0 1 - E 1 1 0)
    (E 2 0 1 - E 2 1 0)
  set t : ℝ := Real.sqrt (p ^ 2 + q ^ 2 + r ^ 2) with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hs
  have ht2 : t ^ 2 = p ^ 2 + q ^ 2 + r ^ 2 := Real.sq_sqrt hs.le
  let v : V3 := ![p, q, r]
  have hv0 : v 0 = p := rfl
  have hv1 : v 1 = q := rfl
  have hv2 : v 2 = r := rfl
  refine ⟨fun l => v l / t, ?_, ?_⟩
  · rw [sq3_eq]
    simp only [hv0, hv1, hv2, div_pow]
    field_simp
    linarith
  · have key : ∀ n : V3, C * nh n * sig 2 * Wᵀ = ∑ l, (n l : ℂ) • E l := by
      intro n
      simp only [hE, nh, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [key]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Fin.sum_univ_three, smul_eq_mul, hv0, hv1, hv2]
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    push_cast
    field_simp
    linear_combination h

theorem det_unit (W : M2) (h : Wᴴ * W = 1) : W.det * conj W.det = 1 := by
  have h' : W * Wᴴ = 1 := mul_eq_one_comm.mp h
  have := congrArg Matrix.det h'
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this
  exact this

theorem K_sym (K : M2) (h : K 0 1 = K 1 0) :
    K = Ksym ((K 0 0 + K 1 1) / 2) (K 0 1) ((K 0 0 - K 1 1) / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ksym, sig, h] <;> ring

theorem tr_reduce (c : Fin 3 → ℝ) (F S0 Φ G : M4) (D : ℂ) (hG : G = D • (S0 * Φ)) :
    (Ug c * F * Ug c * G).trace =
      D * (((Ug c)ᴴ * Φ * Ug c) * (F * (Ug c * S0 * Ug c))).trace := by
  have e1 : ((Ug c)ᴴ * Φ * Ug c) * (F * (Ug c * S0 * Ug c)) =
      ((Ug c)ᴴ * Φ * Ug c * F * Ug c * S0) * Ug c := by simp only [Matrix.mul_assoc]
  have e2 : (Ug c * F * Ug c * G) = D • (Ug c * F * Ug c * S0 * Φ) := by
    rw [hG, Matrix.mul_smul]; simp only [Matrix.mul_assoc]
  have e3 : Ug c * ((Ug c)ᴴ * Φ * Ug c * F * Ug c * S0) = Φ * (Ug c * F * Ug c * S0) := by
    have := Ug_mul_conjT c
    calc Ug c * ((Ug c)ᴴ * Φ * Ug c * F * Ug c * S0)
        = (Ug c * (Ug c)ᴴ) * Φ * (Ug c * F * Ug c * S0) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [this, Matrix.one_mul]
  have key : (Ug c * F * Ug c * S0 * Φ).trace =
      (((Ug c)ᴴ * Φ * Ug c) * (F * (Ug c * S0 * Ug c))).trace := by
    rw [e1, Matrix.trace_mul_comm ((Ug c)ᴴ * Φ * Ug c * F * Ug c * S0) (Ug c), e3,
      Matrix.trace_mul_comm Φ, Matrix.trace_mul_comm (Ug c * F * Ug c * S0)]
  rw [e2, Matrix.trace_smul, smul_eq_mul, key]

theorem fro2_reduce (c : Fin 3 → ℝ) (F S0 Φ G : M4) (D : ℂ) (hG : G = D • (S0 * Φ))
    (hΦ : Φ * Φᴴ = 1) (hD : D * conj D = 1) :
    fro2 (F * Ug c * G) = fro2 (F * (Ug c * S0 * Ug c)) := by
  have hDu : (D • (1 : M4)) * (D • (1 : M4))ᴴ = 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul]
    simp [Complex.star_def, hD]
  have e : F * Ug c * G = (F * Ug c * S0 * Φ) * (D • (1 : M4)) := by
    rw [hG, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, fro2_mul_unitary_right _ _ hDu, fro2_mul_unitary_right _ _ hΦ]
  have e' : F * (Ug c * S0 * Ug c) = (F * Ug c * S0) * Ug c := by simp only [Matrix.mul_assoc]
  rw [e', fro2_mul_unitary_right _ _ (Ug_mul_conjT c)]

end FormalResearch.FrameFree.FTG
