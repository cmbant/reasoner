import FormalResearch.FrameFree.AchiralThree
import FormalResearch.FrameFree.ConverseXi
import FormalResearch.FrameFree.RealRep3Discharge

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix BigOperators
open Matrix FormalResearch.FrameFree.NQubit FormalResearch.FrameFree.Helstrom

/-!
# The exponent ceiling `ξ̄_inv ≤ log 2` for four qubits with a maximally mixed qubit, unconditionally

`thm:expceiling` (`sec4_exceptional.tex`): every four-qubit state with a maximally mixed qubit -- in particular every critical
state (`F_C = 1/2`) -- has an *achiral branch* of weight `1/2`, so `ξ̄_inv ≤ log 2`.

* `Converse.exists_unit_achiral_bra` : for **every** `ψ : Ψ 4` there is a unit `e` with `⟨e|₀ψ` locally-unitarily real
  (`Ach3`).  The three-qubit hyperdeterminant of `s ψ₀ + t ψ₁` is a binary quartic with a root in `ℙ¹`
  (`exists_root_disc`), and `Ach3.of_disc` : `Det = 0 → Ach3`.
* `Converse.achiralBranch_of_mixed` : if `‖⟨e|₀ψ‖² = 1/2` for every unit `e` (i.e. `ρ₀ = I/2`), `AchiralBranch ψ (1/2)`.
* `Converse.mixed_of_FCΘ_half` : unit `ψ : Ψ 4` with `F_C(ψ) = 1/2` has `ρ₀ = I/2` (`ceiling_lmax`, unitary complement).
* `XiInv.xiBarLE_log_two_of_mixed`, `XiInv.critical_xi_inv''` : the converse is discharged;
  `XiInv.xiBarLE_of_marginal_floor` : `ρ₀ ≥ λ ⇒ ξ̄_inv ≤ -log λ`; `XiInv.m4_hasXiInv_log_two` : `ξ_inv(M₄) = log 2`.
-/

namespace FormalResearch.FrameFree.Converse

theorem U2_perp {e : Fin 2 → ℂ} (he : U2 e) : U2 (perp e) := by
  have he : conj (e 0) * e 0 + conj (e 1) * e 1 = 1 := he
  show conj (perp e 0) * perp e 0 + conj (perp e 1) * perp e 1 = 1
  simp only [perp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, map_neg, Complex.conj_conj]
  linear_combination he

/-- **Every four-qubit state has a branch along some unit `e` of qubit 0 that is locally-unitarily real.** -/
theorem exists_unit_achiral_bra (ψ : Ψ 4) : ∃ e : Fin 2 → ℂ, U2 e ∧ Ach3 (bra e ψ) := by
  obtain ⟨s, t, hst, hroot⟩ := exists_root_disc (sl 0 ψ) (sl 1 ψ)
  set β : Ψ 3 := s • sl 0 ψ + t • sl 1 ψ with hβ
  have hβd : disc3R β = 0 := by
    have : β = fun x => s * sl 0 ψ x + t * sl 1 ψ x := by
      funext x; simp [hβ]
    rw [this]; exact hroot
  have hach : Ach3 β := Ach3.of_disc hβd
  set m : ℝ := Complex.normSq s + Complex.normSq t with hm
  have hmpos : 0 < m := by
    rcases hst with h | h
    · have := Complex.normSq_pos.2 h
      have := Complex.normSq_nonneg t
      linarith
    · have := Complex.normSq_pos.2 h
      have := Complex.normSq_nonneg s
      linarith
  set n : ℝ := Real.sqrt m with hn
  have hnpos : 0 < n := Real.sqrt_pos.2 hmpos
  have hn2 : n * n = m := Real.mul_self_sqrt hmpos.le
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  refine ⟨![conj s / n, conj t / n], ?_, ?_⟩
  · show conj (conj s / n) * (conj s / n) + conj (conj t / n) * (conj t / n) = 1
    have h1 : (n : ℂ) * n = (Complex.normSq s : ℂ) + (Complex.normSq t : ℂ) := by
      rw [← Complex.ofReal_mul, hn2, hm]; push_cast; ring
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self] at h1
    simp only [map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    field_simp
    linear_combination -h1
  · have : bra ![conj s / n, conj t / n] ψ = ((n : ℂ)⁻¹) • β := by
      funext y
      simp only [bra, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hβ, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
      field_simp
    rw [this]
    exact hach.smul (inv_ne_zero hnC)

/-- If `ρ₀ = I/2` (`‖⟨e|₀ψ‖² = 1/2` for every unit `e`), then `ψ` has an achiral projected branch of weight `1/2`. -/
theorem achiralBranch_of_mixed (ψ : Ψ 4) (h : ∀ e : Fin 2 → ℂ, U2 e → nsq (bra e ψ) = 1 / 2) :
    AchiralBranch ψ (1 / 2) := by
  obtain ⟨e, he, v, hv, c, hc, hach⟩ := exists_unit_achiral_bra ψ
  have hpos : 0 < nsq (bra e ψ) := by rw [h e he]; norm_num
  have := achiralBranch_of_branch ψ he hv hc hpos hach
  rwa [h e he] at this

/-- Unitary complement: `‖⟨e|₀ψ‖² + ‖⟨e^⊥|₀ψ‖² = ‖ψ‖²`. -/
theorem nsq_bra_add {m : ℕ} (ψ : Ψ (m + 1)) {e : Fin 2 → ℂ} (he : U2 e) :
    nsq (bra e ψ) + nsq (bra (perp e) ψ) = nsq ψ := by
  have he' : conj (e 0) * e 0 + conj (e 1) * e 1 = 1 := he
  have hn := normSq_sum_of_unit he'
  have hn' : (e 0).re * (e 0).re + (e 0).im * (e 0).im + ((e 1).re * (e 1).re + (e 1).im * (e 1).im) = 1 := by
    simpa [Complex.normSq_apply] using hn
  rw [nsq_eq_sum_sl, Fin.sum_univ_two]
  unfold nsq
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  have e1 : bra e ψ y = conj (e 0) * sl 0 ψ y + conj (e 1) * sl 1 ψ y := by
    simp [bra, Fin.sum_univ_two]
  have e2 : bra (perp e) ψ y = e 1 * sl 0 ψ y - e 0 * sl 1 ψ y := by
    simp [bra, Fin.sum_univ_two, perp]; ring
  rw [e1, e2]
  generalize sl 0 ψ y = a
  generalize sl 1 ψ y = b
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  linear_combination (a.re * a.re + a.im * a.im + b.re * b.re + b.im * b.im) * hn'

/-- `‖⟨e|₀ψ‖² ≤ F_C(ψ)` for a four-qubit `ψ` and unit `e` (three-qubit vectors have `F_C ≥ ‖·‖²`). -/
theorem nsq_bra_le_FCΘ (ψ : Ψ 4) {e : Fin 2 → ℂ} (he : U2 e) : nsq (bra e ψ) ≤ Ceilings.FCΘ ψ := by
  have he' : conj (e 0) * e 0 + conj (e 1) * e 1 = 1 := he
  have hb : bra e ψ = Ceilings.peel 0 e ψ := by
    funext y
    simp [bra, Ceilings.peel, sl, Fin.insertNth_zero']
  rw [hb, Ceilings.FCΘ_eq_FC_cj]
  exact (RealRep3Discharge.FC_three_ge' _).trans (Ceilings.peel_le_FC 0 e (normSq_sum_of_unit he') ψ)

/-- A unit four-qubit state with `F_C = 1/2` has `ρ₀ = I/2`. -/
theorem mixed_of_FCΘ_half (ψ : Ψ 4) (hψ : nsq ψ = 1) (hF : Ceilings.FCΘ ψ = 1 / 2) :
    ∀ e : Fin 2 → ℂ, U2 e → nsq (bra e ψ) = 1 / 2 := by
  intro e he
  have h1 := nsq_bra_le_FCΘ ψ he
  have h2 := nsq_bra_le_FCΘ ψ (U2_perp he)
  have h3 := nsq_bra_add ψ he
  rw [hF] at h1 h2
  linarith

end FormalResearch.FrameFree.Converse

namespace FormalResearch.FrameFree.XiInv

open Filter Topology
open FormalResearch.FrameFree.Converse

theorem XiBarLE.mono {n : ℕ} {ψ : Ψ n} {r r' : ℝ} (h : XiBarLE ψ r) (hr : r ≤ r') : XiBarLE ψ r' :=
  fun ε hε => (h ε hε).mono fun _ hk => hk.trans (by linarith)

/-- **`thm:expceiling`, mixed qubit**: `ρ₀ = I/2` gives `ξ̄_inv(ψ) ≤ log 2`. -/
theorem xiBarLE_log_two_of_mixed (ψ : Ψ 4) (h : ∀ e : Fin 2 → ℂ, U2 e → nsq (bra e ψ) = 1 / 2) :
    XiBarLE ψ (Real.log 2) := by
  have := xiBarLE_of_achiral (achiralBranch_of_mixed ψ h)
  rwa [one_div, Real.log_inv, neg_neg] at this

/-- **`thm:expceiling`, universal form**: if `⟨e|ρ₀|e⟩ ≥ λ > 0` for all unit `e` (`λ ≤ λ_min(ρ₀)`), then
`ξ̄_inv(ψ) ≤ -log λ`. -/
theorem xiBarLE_of_marginal_floor (ψ : Ψ 4) {l : ℝ} (hl : 0 < l)
    (h : ∀ e : Fin 2 → ℂ, U2 e → l ≤ nsq (bra e ψ)) : XiBarLE ψ (-Real.log l) := by
  obtain ⟨e, he, v, hv, c, hc, hach⟩ := exists_unit_achiral_bra ψ
  have hpos : 0 < nsq (bra e ψ) := lt_of_lt_of_le hl (h e he)
  have := xiBarLE_of_achiral (achiralBranch_of_branch ψ he hv hc hpos hach)
  refine this.mono ?_
  have := Real.log_le_log hl (h e he)
  linarith

/-- **`thm:expceiling`, critical case, unconditional**: every unit four-qubit state with `F_C = 1/2` has
`ξ_inv = log 2`. -/
theorem critical_xi_inv'' (ψ : Ψ 4) (hψ : nsq ψ = 1) (hF : Ceilings.FCΘ ψ = 1 / 2) :
    HasXiInv ψ (Real.log 2) :=
  critical_xi_inv' hψ hF (xiBarLE_log_two_of_mixed ψ (mixed_of_FCΘ_half ψ hψ hF))

/-- Instance: `ξ_inv(M₄) = log 2`, with neither `h49` nor a converse hypothesis (the support half is
`RealRep3Discharge.FCΘ_M4v_eq'`). -/
theorem m4_hasXiInv_log_two : HasXiInv Ceilings.M4v (Real.log 2) :=
  critical_xi_inv'' Ceilings.M4v Ceilings.nsq_M4v RealRep3Discharge.FCΘ_M4v_eq'

end FormalResearch.FrameFree.XiInv
