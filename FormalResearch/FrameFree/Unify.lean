import FormalResearch.FrameFree.Foundations
import FormalResearch.FrameFree.WeylRealisation
import FormalResearch.FrameFree.PhysicalBridge
import FormalResearch.FrameFree.Ceilings
import FormalResearch.FourQubitEntropy.Checks

/-!
# Linking the three frame-free set-ups (and Paper E's time-reversal quantity)

The repository carries three parallel descriptions of the four-qubit rotation overlap of Paper P:

* `FrameFree/Foundations.lean`  (namespace `FrameFree.NQubit`): `Ψ n`, `rot`, `SU2`, `FK`, `FKΘ`, `Θ`;
* `FrameFree/WeylRealisation.lean`, `PhysicalBridge.lean` (namespace `FrameFree`): `rotOverlap` on
  `FourQubitEntropy.Psi`, `psiMag`, `weyl_le_rotOverlap_conj`, `four_ninths_le_rotOverlap`,
  `FKmag_le_rotOverlap`;
* `FrameFree/Ceilings.lean` (namespace `FrameFree.Ceilings`): the bridge `toN`, `M4v`, and statements
  conditional on `h49 : FKΘ M4v = 4/9`.

This file proves that they agree (everything is **proved**, nothing is assumed):

* `toN_localApply`: `toN (localApply a b c e φ) = NQubit.rot ![a,b,c,e] (toN φ)`, `ip_eq_ip`;
* `rotOverlap_eq_FK`: `rotOverlap ψ φ = NQubit.FK (toN ψ) (toN φ)`;
* `rotOverlap_conj_eq_FKΘ`: `rotOverlap ψ (Psi.conj ψ) = NQubit.FKΘ (toN ψ)`;
* `four_ninths_le_FKΘ_psiMag` (`thm:maxchiral`, lower bound, in `NQubit` form): for every unit critical `q`,
  `4/9 + |qᵀq|²/18 ≤ FKΘ (toN (psiMag q))`; `four_ninths_le_FKΘ_M4v`: `4/9 ≤ FKΘ M4v`, which
  discharges the lower half of the hypothesis `h49` of `Ceilings`: `FKΘ_M4v_eq_of_le` shows that `h49` is
  equivalent to the single upper bound `FKΘ M4v ≤ 4/9` (the recalled input R7), and `CK_M4pow_le`,
  `FKΘ_M4pow_ge` give the unconditional halves of `CK_M4pow` for `M₄^{⊗(m+1)}`.

**Paper E.**  `Tradeoff.lean`/`Purity.lean` of `FourQubitEntropy` use `τ = |ψᵀ ε^{⊗4} ψ|²`
(`spinFlipForm`).  This is exactly the *unrotated* time-reversal overlap: `spinFlip_eq`
(`ψᵀ ε^{⊗4} ψ = conj ⟨ψ|Θψ⟩`), `tau_eq` (`τ = |⟨ψ|Θψ⟩|²`), `tau_le_FKΘ` (`τ ≤ F_K(ψ)`), and, via the purity
identity, `two_mul_purity_sub_le_FKΘ` (`2(P-1) - W₁ ≤ F_K(ψ)` for unit `ψ`) and `purity_eq_one_iff_ip_Θ`
(`P = 1 ⟺ W₁ = 0 ∧ ⟨ψ|Θψ⟩ = 0`).  Paper E's sextic `F` has no time-reversal content and is not related here.

Name hygiene: `FrameFree.ip`/`SU2` (four-qubit) and `NQubit.ip`/`SU2` are both used, always qualified.
-/

open scoped ComplexConjugate Matrix BigOperators

namespace FormalResearch.FrameFree.Unify

open FormalResearch.FourQubitEntropy

/-! ### The bridge `Psi ≃ Ψ 4` and the local action -/

/-- `Fin 2 ^ 4` as a four-fold product. -/
def e4 : (Fin 4 → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 × Fin 2 :=
  { toFun := fun x => (x 0, x 1, x 2, x 3)
    invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
    left_inv := fun x => by funext i; fin_cases i <;> rfl
    right_inv := fun p => rfl }

theorem sum_e4 (f : (Fin 4 → Fin 2) → ℂ) :
    ∑ x, f x = ∑ a, ∑ b, ∑ c, ∑ d, f ![a, b, c, d] := by
  rw [← e4.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

/-- The bridge `FourQubitEntropy.Psi → NQubit.Ψ 4` (that of `Ceilings`). -/
abbrev toN : Psi → NQubit.Ψ 4 := Ceilings.toN

theorem toN_apply (ψ : Psi) (x : Fin 4 → Fin 2) : toN ψ x = ψ (x 0) (x 1) (x 2) (x 3) := rfl

theorem toN_cons (ψ : Psi) (a b c d : Fin 2) : toN ψ ![a, b, c, d] = ψ a b c d := rfl

theorem toN_conj (ψ : Psi) : toN (Psi.conj ψ) = NQubit.cj (toN ψ) := rfl

/-- The two `SU(2)` predicates agree. -/
theorem su2_iff (a : Op1) : SU2 a ↔ NQubit.SU2 a := Iff.rfl

/-- The four-qubit pairing is the `NQubit` pairing. -/
theorem ip_eq_ip (ψ φ : Psi) : ip ψ φ = NQubit.ip (toN ψ) (toN φ) := by
  rw [NQubit.ip, sum_e4]
  simp [ip, toN_cons]

theorem nsq_toN (ψ : Psi) : NQubit.nsq (toN ψ) = normSqPsi ψ := Ceilings.nsq_toN ψ

theorem toN_localApply (a b c e : Op1) (φ : Psi) :
    toN (localApply a b c e φ) = NQubit.rot ![a, b, c, e] (toN φ) := by
  funext x
  rw [toN_apply, localApply_apply, NQubit.rot, sum_e4]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  rw [Fin.prod_univ_four]
  rfl

theorem rot_eq_cons (u : Fin 4 → Op1) : u = ![u 0, u 1, u 2, u 3] := by
  funext i; fin_cases i <;> rfl

/-! ### `rotOverlap = FK` -/

/-- **`rotOverlap` is `NQubit.FK`.** -/
theorem rotOverlap_eq_FK (ψ φ : Psi) : rotOverlap ψ φ = NQubit.FK (toN ψ) (toN φ) := by
  unfold rotOverlap NQubit.FK
  congr 1
  ext r
  constructor
  · rintro ⟨a, b, c, e, ha, hb, hc, he, rfl⟩
    refine ⟨![a, b, c, e], ?_, ?_⟩
    · intro i; fin_cases i <;> assumption
    · rw [ip_eq_ip, toN_localApply]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u 0, u 1, u 2, u 3, hu 0, hu 1, hu 2, hu 3, ?_⟩
    rw [ip_eq_ip, toN_localApply, ← rot_eq_cons]

/-- `F_K(ψ, ψ̄)` of the four-qubit set-up is `NQubit.FKΘ`. -/
theorem rotOverlap_conj_eq_FKΘ (ψ : Psi) :
    rotOverlap ψ (Psi.conj ψ) = NQubit.FKΘ (toN ψ) := by
  rw [rotOverlap_eq_FK, toN_conj, ← NQubit.FKΘ_eq_FK_cj]

/-! ### `thm:maxchiral` (lower bound) in the `NQubit` set-up, and the lower half of `h49` -/

theorem nsq_toN_psiMag (q : Fin 4 → ℂ) : NQubit.nsq (toN (psiMag q)) = nrm2 q := by
  have h := NQubit.ip_self (toN (psiMag q))
  rw [← ip_eq_ip, ip_psiMag] at h
  have h2 : ((nrm2 q : ℝ) : ℂ) = ∑ k, conj (q k) * q k := by
    unfold nrm2; push_cast
    exact Finset.sum_congr rfl fun k _ => by rw [Complex.normSq_eq_conj_mul_self]
  rw [← h2] at h
  exact_mod_cast h.symm

/-- The Weyl-vertex value is a lower bound for `NQubit.FKΘ` of the magic-diagonal state. -/
theorem FKmag_le_FKΘ (q : Fin 4 → ℂ) : FKmag q ≤ NQubit.FKΘ (toN (psiMag q)) := by
  rw [← rotOverlap_conj_eq_FKΘ]; exact FKmag_le_rotOverlap q

/-- **`thm:maxchiral`, lower bound** (`NQubit` form).  For every unit critical coefficient vector `q`,
`F_K(ψ_q) ≥ 4/9 + |qᵀq|²/18`. -/
theorem maxchiral_le_FKΘ (q : Fin 4 → ℂ) (hq : nrm2 q = 1) :
    4 / 9 + Complex.normSq (bdot q q) / 18 ≤ NQubit.FKΘ (toN (psiMag q)) :=
  (FKmag_ge_maxchiral' q hq).trans (FKmag_le_FKΘ q)

theorem four_ninths_le_FKΘ_psiMag (q : Fin 4 → ℂ) (hq : nrm2 q = 1) :
    (4 / 9 : ℝ) ≤ NQubit.FKΘ (toN (psiMag q)) :=
  (FKmag_ge_four_ninths' q hq).trans (FKmag_le_FKΘ q)

/-- `M4v = toN M₄` and `F_K(M₄) ≥ 4/9` in the `NQubit` form used by `Ceilings`. -/
theorem four_ninths_le_FKΘ_M4v : (4 / 9 : ℝ) ≤ NQubit.FKΘ Ceilings.M4v := by
  have := four_ninths_le_rotOverlap_M4
  rwa [rotOverlap_conj_eq_FKΘ] at this

/-- The hypothesis `h49` of `Ceilings` is equivalent to the single upper bound `F_K(M₄) ≤ 4/9`
(the recalled input R7). -/
theorem FKΘ_M4v_eq_iff : NQubit.FKΘ Ceilings.M4v = 4 / 9 ↔ NQubit.FKΘ Ceilings.M4v ≤ 4 / 9 :=
  ⟨fun h => h.le, fun h => le_antisymm h four_ninths_le_FKΘ_M4v⟩

theorem FKΘ_M4v_eq_of_le (h : NQubit.FKΘ Ceilings.M4v ≤ 4 / 9) : NQubit.FKΘ Ceilings.M4v = 4 / 9 :=
  FKΘ_M4v_eq_iff.2 h

/-- `M₄` is uncalibrated given only the upper bound on `F_K(M₄)`. -/
theorem M4_uncalibrated_of_le (hR : Ceilings.RealRep3) (h : NQubit.FKΘ Ceilings.M4v ≤ 4 / 9) :
    NQubit.FKΘ Ceilings.M4v < Ceilings.FCΘ Ceilings.M4v :=
  Ceilings.M4_uncalibrated hR (FKΘ_M4v_eq_of_le h)

/-- `F_K(M₄^{⊗(m+1)}) ≥ (4/9)^{m+1}`, unconditionally. -/
theorem FKΘ_M4pow_ge (m : ℕ) : (4 / 9 : ℝ) ^ (m + 1) ≤ NQubit.FKΘ (Ceilings.M4pow m) := by
  induction m with
  | zero => show (4 / 9 : ℝ) ^ (0 + 1) ≤ NQubit.FKΘ Ceilings.M4v; simpa using four_ninths_le_FKΘ_M4v
  | succ m ih =>
    show (4 / 9 : ℝ) ^ (m + 1 + 1) ≤ NQubit.FKΘ (NQubit.tens (Ceilings.M4pow m) Ceilings.M4v)
    rw [NQubit.FKΘ_tens, pow_succ]
    exact mul_le_mul ih four_ninths_le_FKΘ_M4v (by norm_num) (NQubit.FK_nonneg _ _)

/-- `C_K(M₄^{⊗(m+1)}) ≤ (m+1) log(9/4)`, unconditionally (the other half is `Ceilings.CK_M4pow`). -/
theorem CK_M4pow_le (m : ℕ) : NQubit.CK (Ceilings.M4pow m) ≤ (m + 1) * Real.log (9 / 4) := by
  unfold NQubit.CK
  have hpos : (0 : ℝ) < (4 / 9) ^ (m + 1) := by positivity
  have h := Real.log_le_log hpos (FKΘ_M4pow_ge m)
  rw [Real.log_pow] at h
  have : Real.log (4 / 9 : ℝ) = - Real.log (9 / 4) := by
    rw [← Real.log_inv]; norm_num
  rw [this] at h
  push_cast at h
  linarith

/-! ### Paper E's `τ = |ψᵀ ε^{⊗4} ψ|²` is the unrotated time-reversal overlap -/

theorem toN_one_sub (ψ : Psi) (a b c d : Fin 2) :
    toN ψ (fun i => 1 - ![a, b, c, d] i) = ψ (1 - a) (1 - b) (1 - c) (1 - d) := rfl

theorem eps_apply (a b : Fin 2) :
    NQubit.eps a b = if b = 1 - a then (if a = 0 then 1 else -1) else 0 := by
  fin_cases a <;> fin_cases b <;> simp [NQubit.eps]

/-- `(Θφ)_x = (∏ᵢ (-1)^{xᵢ}) · conj φ_{1-x}`. -/
theorem Θ_apply (φ : NQubit.Ψ 4) (x : Fin 4 → Fin 2) :
    NQubit.Θ φ x = (∏ i, (if x i = 0 then (1 : ℂ) else -1)) * conj (φ (fun i => 1 - x i)) := by
  unfold NQubit.Θ
  rw [Finset.sum_eq_single (fun i => 1 - x i)]
  · congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [eps_apply]; simp
  · intro y _ hy
    have : ∃ i, y i ≠ 1 - x i := by
      by_contra h
      push Not at h
      exact hy (funext h)
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · simp
    · rw [eps_apply]; simp [hi]
  · simp

/-- Paper E's `ψᵀ ε^{⊗4} ψ` (`spinFlipForm`) is `conj ⟨ψ|Θψ⟩`. -/
theorem spinFlip_eq (ψ : Psi) :
    spinFlipForm ψ = conj (NQubit.ip (toN ψ) (NQubit.Θ (toN ψ))) := by
  rw [NQubit.ip, map_sum, sum_e4]
  simp only [Θ_apply, map_mul, Complex.conj_conj]
  simp only [spinFlipForm, sum4, sum2, Fin.sum_univ_two]
  have h0 : FourQubitEntropy.sgn 0 = 1 := by simp [FourQubitEntropy.sgn]
  have h1 : FourQubitEntropy.sgn 1 = -1 := by simp [FourQubitEntropy.sgn]
  have s0 : (1 : Fin 2) - 0 = 1 := by decide
  simp [toN_one_sub, toN_cons, h0, h1, s0, Fin.prod_univ_four]

/-- Paper E's `τ(ψ)` equals `|⟨ψ|Θψ⟩|²`. -/
theorem tau_eq (ψ : Psi) :
    Complex.normSq (spinFlipForm ψ) = Complex.normSq (NQubit.ip (toN ψ) (NQubit.Θ (toN ψ))) := by
  rw [spinFlip_eq, Complex.normSq_conj]

/-- `τ(ψ) ≤ F_K(ψ)`: Paper E's `τ` is the `u = 1` term of the rotation overlap. -/
theorem tau_le_FKΘ (ψ : Psi) : Complex.normSq (spinFlipForm ψ) ≤ NQubit.FKΘ (toN ψ) := by
  rw [tau_eq]; exact NQubit.le_FKΘ_one _

/-- For unit `ψ`: `2(P - 1) - W₁ ≤ F_K(ψ)` (the purity identity `2P = 2 + W₁ + τ` and `τ ≤ F_K`). -/
theorem two_mul_purity_sub_le_FKΘ (ψ : Psi) (hn : normSqPsi ψ = 1) :
    2 * (purity ψ - 1) - blochSq ψ ≤ NQubit.FKΘ (toN ψ) := by
  have h := purity_identity_exact ψ
  rw [hn] at h
  have := tau_le_FKΘ ψ
  linarith

/-- For unit `ψ`: `P = 1` iff `W₁ = 0` and `⟨ψ|Θψ⟩ = 0`. -/
theorem purity_eq_one_iff_ip_Θ (ψ : Psi) (hn : normSqPsi ψ = 1) :
    purity ψ = 1 ↔ blochSq ψ = 0 ∧ NQubit.ip (toN ψ) (NQubit.Θ (toN ψ)) = 0 := by
  rw [purity_eq_one_iff ψ hn, spinFlip_eq, map_eq_zero]

/-- `C_K(ψ) ≤ -log τ(ψ)` whenever `τ(ψ) > 0`. -/
theorem CK_le_neg_log_tau (ψ : Psi) (hτ : 0 < Complex.normSq (spinFlipForm ψ)) :
    NQubit.CK (toN ψ) ≤ - Real.log (Complex.normSq (spinFlipForm ψ)) := by
  unfold NQubit.CK
  have := Real.log_le_log hτ (tau_le_FKΘ ψ)
  linarith

end FormalResearch.FrameFree.Unify
