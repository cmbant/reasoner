import FormalResearch.FrameFree.PolyImageDischarge
import FormalResearch.FrameFree.PsiPlusKramers
import FormalResearch.FrameFree.RealRep3Discharge
import FormalResearch.FrameFree.Reversals

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Filter Topology
open scoped Real
open FormalResearch.FrameFree.NQubit FormalResearch.FrameFree.Helstrom
open FormalResearch.FrameFree

/-!
# The operational exponent `ξ_inv` without the support-rate hypothesis

Namespace `FormalResearch.FrameFree.XiInv`.  `SupportRate.supportRateUpper` (`PolyImageDischarge`) proves the hard half of
`thm:supportrate` for every `ψ`, so the hypothesis `Helstrom.SupportRateUpper ψ`, and the free variable `ξ`
bounded below by `-log F_C` in `Reversals`, `RealRep3Discharge`, `PsiPlusKramers`, are no longer needed.

* `HasXiInv ψ ξ` : `-(1/k) log P_e(k) → ξ` (the exponent `ξ_inv(ψ) = ξ`; `P_e = Helstrom.Pe`).
* `XiBarLE ψ r` : `limsup -(1/k) log P_e(k) ≤ r` in `ε`-form (the converse hypothesis, `Reversals.RateLE`).
* `negLog_FC_le_of_hasXiInv`: `-log F_C(ψ) ≤ ξ_inv(ψ)` whenever the limit exists (`thm:supportrate`).
* `hasXiInv_of_xiBarLE`: converse `ξ̄_inv ≤ -log F_C` gives `ξ_inv = -log F_C`.
* `psiplus_xi_inv'`, `Phi8_xi_inv'` (unconditional), `exchange_xi_inv'` (`thm:heis`, under the exchange bounds),
  `m4_exponent'`, `blocks_exponent'`, `critical_exponent'` (`thm:expceiling`, `thm:m4exponent`, converse as hypothesis),
  `eight_qubit_reversal_xi'`, `gap_reversal_xi'`, `fourgate_*'`, `region_reversal'`, `tens_xi_inv'`.

Hypotheses that remain are exactly those in each statement: a converse (`XiBarLE`, or `ξ ≤ …`), `Sharing.ExchangeIndepBound(C) θ`,
`FKΘ M₄ ≤ 4/9` (R7 upper half), the Helstrom product inequality `P_⊗ ≥ ½ ∏ P_i` (not formalised) and the envelope
bound at `U_*`.  Later files discharge some of them: the converse for `M₄`, its powers and every critical four-qubit
state (`ConverseXi.blocks_hasXiInv`, `AchiralCritical.critical_xi_inv''`, `m4_hasXiInv_log_two`) and the exchange
bounds for `0 ≤ θ ≤ π/4` (`ExchangeBounds`, `ExchangeBoundsWrappers`).
-/

namespace FormalResearch.FrameFree.XiInv

/-- `ξ_inv(ψ) = ξ`: the exponent of the frame-free invariant error exists and equals `ξ`. -/
def HasXiInv {n : ℕ} (ψ : Ψ n) (ξ : ℝ) : Prop :=
  Tendsto (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (Pe k ψ)) atTop (𝓝 ξ)

/-- `limsup_k -(1/k) log P_e(k) ≤ r` (`ε`-form): an upper bound for the exponent (the converse side). -/
def XiBarLE {n : ℕ} (ψ : Ψ n) (r : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, -(1 / (k : ℝ)) * Real.log (Pe k ψ) ≤ r + ε

theorem xiBarLE_iff_rateLE {n : ℕ} (ψ : Ψ n) (r : ℝ) :
    XiBarLE ψ r ↔ Reversals.RateLE (fun k => Pe k ψ) r := by
  have e : ∀ k : ℕ, -(1 / (k : ℝ)) * Real.log (Pe k ψ) = -Real.log (Pe k ψ) / k := fun k => by ring
  unfold XiBarLE Reversals.RateLE
  simp only [e]

theorem HasXiInv.unique {n : ℕ} {ψ : Ψ n} {ξ ξ' : ℝ} (h : HasXiInv ψ ξ) (h' : HasXiInv ψ ξ') :
    ξ = ξ' := tendsto_nhds_unique h h'

theorem HasXiInv.xiBarLE {n : ℕ} {ψ : Ψ n} {ξ : ℝ} (h : HasXiInv ψ ξ) : XiBarLE ψ ξ := fun ε hε =>
  h.eventually (Iio_mem_nhds (by linarith : ξ < ξ + ε)) |>.mono fun _ hk => hk.le

/-- **`thm:window`, upper half**, in `XiBarLE` form: `ξ̄_inv ≤ C_K` for every unit `ψ`. -/
theorem xiBarLE_CK {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) : XiBarLE ψ (CK ψ) := fun ε hε =>
  eventually_neg_log_Pe_le ψ hψ (by linarith : CK ψ < CK ψ + ε)

/-! ### The support test, unconditionally -/

/-- `thm:supportrate` (second sentence): for `c > F_C(ψ)`, eventually `-(1/k) log P_e(k) ≥ -log c`. -/
theorem eventually_negLog_c_le {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) {c : ℝ}
    (hc : Ceilings.FCΘ ψ < c) :
    ∀ᶠ k : ℕ in atTop, -Real.log c ≤ -(1 / (k : ℝ)) * Real.log (Pe k ψ) :=
  eventually_neg_log_c_le ψ hψ (SupportRate.supportRateUpper ψ) hc

/-- **`ξ_inv ≥ -log F_C`** (`thm:supportrate`), unconditional: if the exponent exists it is at least `-log F_C`. -/
theorem negLog_FC_le_of_hasXiInv {n : ℕ} {ψ : Ψ n} {ξ : ℝ} (hψ : nsq ψ = 1)
    (hpos : 0 < Ceilings.FCΘ ψ) (h : HasXiInv ψ ξ) : -Real.log (Ceilings.FCΘ ψ) ≤ ξ := by
  have key : ∀ c, Ceilings.FCΘ ψ < c → -Real.log c ≤ ξ := fun c hc =>
    ge_of_tendsto h (eventually_negLog_c_le ψ hψ hc)
  by_contra hlt
  rw [not_le] at hlt
  set F := Ceilings.FCΘ ψ with hF
  set δ := (-Real.log F - ξ) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hexp : 1 < Real.exp δ := by simpa using Real.exp_lt_exp.2 hδpos
  have hc : F < F * Real.exp δ := by nlinarith
  have := key _ hc
  rw [Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  linarith

/-- **Converse + support test = exponent.**  If `ξ̄_inv(ψ) ≤ r` and `-log F_C(ψ) = r` (with `F_C > 0`),
then `ξ_inv(ψ)` exists and equals `r`. -/
theorem hasXiInv_of_xiBarLE {n : ℕ} {ψ : Ψ n} {r : ℝ} (hψ : nsq ψ = 1)
    (hpos : 0 < Ceilings.FCΘ ψ) (hr : -Real.log (Ceilings.FCΘ ψ) = r) (hhi : XiBarLE ψ r) :
    HasXiInv ψ r := by
  rw [HasXiInv, tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · set F := Ceilings.FCΘ ψ with hF
    set δ := (r - a) / 2 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have hexp : 1 < Real.exp δ := by simpa using Real.exp_lt_exp.2 hδpos
    have hc : F < F * Real.exp δ := by nlinarith
    have hlog : -Real.log (F * Real.exp δ) = r - δ := by
      rw [Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]; linarith
    filter_upwards [eventually_negLog_c_le ψ hψ hc] with k hk
    linarith
  · filter_upwards [hhi ((b - r) / 2) (by linarith)] with k hk
    linarith

/-- **`cor:calibrated`**, in `HasXiInv` form (unconditional): `F_C = F_K` gives `ξ_inv = C_K`. -/
theorem hasXiInv_of_calibrated {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1)
    (hcal : Ceilings.FCΘ ψ = FKΘ ψ) : HasXiInv ψ (CK ψ) :=
  SupportRate.tendsto_of_calibrated ψ hψ hcal

/-! ### `ψ₊` and `ψ₊ ⊗ ψ₊` -/

/-- **`thm:psipluskramers`, rate** (replaces `PsiPlusKramers.psiplus_xi_inv`, unconditional):
`ξ_inv(ψ₊) = log 2`. -/
theorem psiplus_xi_inv' : HasXiInv PsiPlusKramers.psiPlus (Real.log 2) := by
  have h := hasXiInv_of_calibrated PsiPlusKramers.psiPlus (Sharing.nsq_psiEx _)
    PsiPlusKramers.psiplus_calibrated
  rwa [PsiPlusKramers.psiplus_CK] at h

theorem Phi8_calibrated : Ceilings.FCΘ Reversals.Phi8 = FKΘ Reversals.Phi8 := by
  obtain ⟨hc, hk⟩ : Ceilings.FCΘ (Sharing.psiEx (π / 4)) = 1 / 2 ∧ FKΘ (Sharing.psiEx (π / 4)) = 1 / 2 :=
    PsiPlusKramers.psiplus_kramers
  unfold Reversals.Phi8
  rw [NQubit.FKΘ_tens, Ceilings.FCΘ_tens _ _ (by rw [Sharing.nsq_psiEx]; norm_num)
    (by rw [Sharing.nsq_psiEx]; norm_num), hc, hk]

theorem nsq_Phi8 : nsq Reversals.Phi8 = 1 := by
  unfold Reversals.Phi8; rw [nsq_tens, Sharing.nsq_psiEx, one_mul]

theorem nsq_Psi8 (θ : ℝ) : nsq (Reversals.Psi8 θ) = 1 := by
  unfold Reversals.Psi8; rw [nsq_tens, Ceilings.nsq_M4v, Sharing.nsq_psiEx, one_mul]

/-- **`cor:calgeom-spin1extensive` (b), the comparator** (unconditional): `ξ_inv(ψ₊ ⊗ ψ₊) = log 4 = C_K`. -/
theorem Phi8_xi_inv' : HasXiInv Reversals.Phi8 (Real.log 4) := by
  have h := hasXiInv_of_calibrated _ nsq_Phi8 Phi8_calibrated
  rwa [(PsiPlusKramers.Phi8_values').1] at h

/-! ### The exchange law (`thm:heis`) and the calibrated ruler -/

/-- **`thm:heis`, exponent**, `0 ≤ θ ≤ π/4`, under the two recalled exchange bounds (`cor:ftg`; proved
at `θ = π/4`): `ξ_inv(ψ_{U_θ}) = C_K = -log F_C = log (2/(1+cos 2θ))`. -/
theorem exchange_xi_inv' {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4) (hK : Sharing.ExchangeIndepBound θ)
    (hC : Sharing.ExchangeIndepBoundC θ) :
    HasXiInv (Sharing.psiEx θ) (Reversals.CKex (Real.cos (2 * θ))) ∧
      CK (Sharing.psiEx θ) = Reversals.CKex (Real.cos (2 * θ)) ∧
      -Real.log (Ceilings.FCΘ (Sharing.psiEx θ)) = Reversals.CKex (Real.cos (2 * θ)) := by
  obtain ⟨hfc, hfk, -, hxi, hck⟩ := Reversals.exchange_law h0 h1 hK hC
  have h := hasXiInv_of_calibrated (Sharing.psiEx θ) (Sharing.nsq_psiEx θ) (hfc.trans hfk.symm)
  rw [hck] at h
  exact ⟨h, hck, hxi⟩

/-- The exchange gates are an *operational* calibrated ruler on `[0, log 2]`: for every `r ∈ [0, log 2]`
there is `θ ∈ [0, π/4]` with `ξ_inv(ψ_{U_θ}) = C_K(ψ_{U_θ}) = r`.  Remaining hypothesis: the exchange
bounds for all `θ ∈ [0, π/4]` (`cor:ftg`). -/
theorem exchange_ruler_xi'
    (hex : ∀ θ : ℝ, 0 ≤ θ → θ ≤ π / 4 → Sharing.ExchangeIndepBound θ ∧ Sharing.ExchangeIndepBoundC θ)
    {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ Real.log 2) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ π / 4 ∧ HasXiInv (Sharing.psiEx θ) r ∧ CK (Sharing.psiEx θ) = r := by
  obtain ⟨θ, t0, t1, ht⟩ := Reversals.exchange_ruler h0 h1
  obtain ⟨hx, hc, -⟩ := exchange_xi_inv' t0 t1 (hex θ t0 t1).1 (hex θ t0 t1).2
  rw [ht] at hx hc
  exact ⟨θ, t0, t1, hx, hc⟩

/-- **Gaps give reversals** (`s4-reversals`), operationally: if `ξ_inv(ψ) = ξ ≥ 0` and `ξ < C_K(ψ) ≤ log 2`,
there is an exchange gate `θ ∈ [0, π/4]` whose Choi state has `C_K(ψ_{U_θ}) = ξ_inv(ψ_{U_θ}) = ξ'` with
`(C_K(ψ), ξ)` a strict reversal against `(ξ', ξ')`.  Remaining hypothesis: the exchange bounds. -/
theorem gap_reversal_xi'
    (hex : ∀ θ : ℝ, 0 ≤ θ → θ ≤ π / 4 → Sharing.ExchangeIndepBound θ ∧ Sharing.ExchangeIndepBoundC θ)
    {n : ℕ} {ψ : Ψ n} {ξ : ℝ} (_hξ : HasXiInv ψ ξ) (hξ0 : 0 ≤ ξ) (hgap : ξ < CK ψ)
    (hC : CK ψ ≤ Real.log 2) :
    ∃ θ ξ' : ℝ, 0 ≤ θ ∧ θ ≤ π / 4 ∧ HasXiInv (Sharing.psiEx θ) ξ' ∧
      Reversals.StrictReversal (CK ψ) ξ (CK (Sharing.psiEx θ)) ξ' := by
  obtain ⟨θ, t0, t1, hx, hc⟩ := exchange_ruler_xi' hex (r := (ξ + CK ψ) / 2) (by linarith) (by linarith)
  refine ⟨θ, (ξ + CK ψ) / 2, t0, t1, hx, ?_⟩
  rw [hc]
  exact Reversals.reversal_of_gap_ruler hgap (by linarith) (by linarith)

/-! ### Gate reversals

The exponent of `U_*` is not an operational object in the repository (`CKg c = -log FKmag (dgate c)` is the
Weyl-side quantity; the Choi state of a general gate is not identified with it), so for `U_*` the exponent `ξ`
stays a free real bounded above by the converse (`ξ ≤ B_*` or `EnvelopeAtStar ξ`), exactly as in `Reversals`.
Only the exchange comparator, whose exponent is `ξ_inv(ψ_{U_θ})`, becomes operational. -/

/-- **`thm:calgeom-fourgate`**, exchange comparator operational: `ξ(U_*) ≤ B_* = 0.42776639` (converse, a
hypothesis) and `0.28672 ≤ s = cos 2θ ≤ 0.30392` give
`C_K(U_*) > C_K(ψ_{U_θ}) = ξ_inv(ψ_{U_θ}) > ξ(U_*)`. -/
theorem fourgate_reversal_window' {θ ξ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4)
    (hK : Sharing.ExchangeIndepBound θ) (hC : Sharing.ExchangeIndepBoundC θ)
    (hξ : ξ ≤ 0.42776639) (hs1 : 0.28672 ≤ Real.cos (2 * θ)) (hs2 : Real.cos (2 * θ) ≤ 0.30392) :
    HasXiInv (Sharing.psiEx θ) (Reversals.CKex (Real.cos (2 * θ))) ∧
      Reversals.StrictReversal (Reversals.CKg Reversals.cStar) ξ (CK (Sharing.psiEx θ))
        (Reversals.CKex (Real.cos (2 * θ))) := by
  obtain ⟨hx, hc, -⟩ := exchange_xi_inv' h0 h1 hK hC
  refine ⟨hx, ?_⟩
  rw [hc]
  exact Reversals.fourgate_reversal_window hξ hs1 hs2

/-- **`thm:calgeom-fourgate`, self-certified**: from `EnvelopeAtStar ξ` and `0.28672 ≤ cos 2θ < 0.3034`. -/
theorem fourgate_reversal_certified' {θ ξ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4)
    (hK : Sharing.ExchangeIndepBound θ) (hC : Sharing.ExchangeIndepBoundC θ)
    (hξ : Reversals.EnvelopeAtStar ξ) (hs1 : 0.28672 ≤ Real.cos (2 * θ))
    (hs2 : Real.cos (2 * θ) < 0.3034) :
    HasXiInv (Sharing.psiEx θ) (Reversals.CKex (Real.cos (2 * θ))) ∧
      Reversals.StrictReversal (Reversals.CKg Reversals.cStar) ξ (CK (Sharing.psiEx θ))
        (Reversals.CKex (Real.cos (2 * θ))) := by
  obtain ⟨hx, hc, -⟩ := exchange_xi_inv' h0 h1 hK hC
  refine ⟨hx, ?_⟩
  rw [hc]
  exact Reversals.fourgate_reversal_certified hξ hs1 hs2

/-- **`thm:calgeom-fourgate` at `s = 3/10`**: `C_K(ψ_{U_θ}) = ξ_inv(ψ_{U_θ}) = log (20/13) ∈ (0.43078, 0.43079)`,
both margins exceed `0.0030`, and `(C_K(U_*), ξ(U_*))` is a strict reversal against it. -/
theorem fourgate_three_tenths' {θ ξ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4)
    (hK : Sharing.ExchangeIndepBound θ) (hC : Sharing.ExchangeIndepBoundC θ)
    (hs : Real.cos (2 * θ) = 3 / 10) (hξ : ξ ≤ 0.42776639) :
    HasXiInv (Sharing.psiEx θ) (Real.log (20 / 13)) ∧ CK (Sharing.psiEx θ) = Real.log (20 / 13) ∧
      0.43078 < Real.log (20 / 13) ∧ Real.log (20 / 13) < 0.43079 ∧
      0.0030 < Reversals.CKg Reversals.cStar - Real.log (20 / 13) ∧
      0.0030 < Real.log (20 / 13) - ξ ∧
      Reversals.StrictReversal (Reversals.CKg Reversals.cStar) ξ (CK (Sharing.psiEx θ))
        (Real.log (20 / 13)) := by
  obtain ⟨hx, hc, -⟩ := exchange_xi_inv' h0 h1 hK hC
  rw [hs, Reversals.CKex_three_tenths] at hx hc
  obtain ⟨-, l1, l2, m1, m2, rev⟩ := Reversals.fourgate_three_tenths hξ
  rw [Reversals.CKex_three_tenths] at l1 l2 m1 m2 rev
  refine ⟨hx, hc, l1, l2, m1, m2, ?_⟩
  rw [hc]; exact rev

/-- **`thm:ratefailregion` / `thm:calgeom-fourgate`, region reversals**: for a gate in the region with (R3),
a free `ξ ≥ 0` obeying the envelope bound (converse, a hypothesis) and `C_K ≤ log 2`, there is an exchange
gate `θ` whose operational exponent `ξ' = ξ_inv(ψ_{U_θ})` forms a strict reversal with it.  Remaining
hypotheses: the envelope bound and the exchange bounds. -/
theorem region_reversal'
    (hex : ∀ θ : ℝ, 0 ≤ θ → θ ≤ π / 4 → Sharing.ExchangeIndepBound θ ∧ Sharing.ExchangeIndepBoundC θ)
    (c : Fin 3 → ℝ) (h0 : 0 < |c 2|) (h1 : |c 2| < c 1) (h2 : c 1 < c 0)
    (h3 : c 0 + |c 2| < π / 4)
    (hR3 : Real.cos (4 * c 2) < Real.cos (2 * c 1) * Real.cos (2 * c 2)) {ξ : ℝ} (hξ0 : 0 ≤ ξ)
    (hξ : ∀ u : ℝ, 1 ≤ u → Reversals.rlf (Real.cos (2 * c 2)) (Real.cos (2 * c 1)) u ≤ Real.exp (-ξ))
    (hC : Reversals.CKg c ≤ Real.log 2) :
    ∃ θ ξ' : ℝ, 0 ≤ θ ∧ θ ≤ π / 4 ∧ HasXiInv (Sharing.psiEx θ) ξ' ∧
      Reversals.StrictReversal (Reversals.CKg c) ξ (CK (Sharing.psiEx θ)) ξ' := by
  obtain ⟨θ, t0, t1, hrev⟩ := Reversals.region_reversal c h0 h1 h2 h3 hR3 hξ0 hξ hC
  obtain ⟨hx, hc, -⟩ := exchange_xi_inv' t0 t1 (hex θ t0 t1).1 (hex θ t0 t1).2
  refine ⟨θ, _, t0, t1, hx, ?_⟩
  rw [hc]; exact hrev

/-! ### The exponent ceiling, `M₄`, blocks of four -/

/-- **`thm:expceiling`, last sentence**: a unit state with `F_C = 1/2` and converse
`ξ̄_inv ≤ log 2` has `ξ_inv = log 2`.  The converse (the symmetric-sector bound `ξ̄ ≤ log(λmax/λmin²)`) remains a
hypothesis. -/
theorem critical_xi_inv' {n : ℕ} {ψ : Ψ n} (hψ : nsq ψ = 1) (hF : Ceilings.FCΘ ψ = 1 / 2)
    (hhi : XiBarLE ψ (Real.log 2)) : HasXiInv ψ (Real.log 2) :=
  hasXiInv_of_xiBarLE hψ (by rw [hF]; norm_num)
    (by rw [hF, one_div, Real.log_inv, neg_neg]) hhi

/-- `Reversals.critical_exponent` with the support lower bound discharged. -/
theorem critical_exponent' {n : ℕ} {ψ : Ψ n} {ξ : ℝ} (hψ : nsq ψ = 1) (hF : Ceilings.FCΘ ψ = 1 / 2)
    (hξ : HasXiInv ψ ξ) (hhi : ξ ≤ Real.log 2) : ξ = Real.log 2 :=
  Reversals.critical_exponent hF
    (negLog_FC_le_of_hasXiInv hψ (by rw [hF]; norm_num) hξ) hhi

/-- **`thm:m4exponent`** (`F_K(M₄) ≤ 4/9`, R7 upper half; converse `ξ̄_inv(M₄) ≤ log 2` = `thm:expceiling`):
`ξ_inv(M₄) = log 2 < C_K(M₄) = log (9/4)`, `C_K - ξ = log (9/8)`, fraction `∈ (0.1452, 0.1453)`. -/
theorem m4_xi_inv' (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) (hhi : XiBarLE Ceilings.M4v (Real.log 2)) :
    HasXiInv Ceilings.M4v (Real.log 2) ∧ CK Ceilings.M4v = Real.log (9 / 4) ∧
      Real.log 2 < CK Ceilings.M4v ∧ CK Ceilings.M4v - Real.log 2 = Real.log (9 / 8) ∧
      0.1452 < 1 - Real.log 2 / CK Ceilings.M4v ∧ 1 - Real.log 2 / CK Ceilings.M4v < 0.1453 := by
  have hx := critical_xi_inv' Ceilings.nsq_M4v RealRep3Discharge.FCΘ_M4v_eq' hhi
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := RealRep3Discharge.m4_exponent' h49 (Real.log 2)
    (negLog_FC_le_of_hasXiInv Ceilings.nsq_M4v (by rw [RealRep3Discharge.FCΘ_M4v_eq']; norm_num) hx)
    le_rfl
  exact ⟨hx, h2, h3, h4, h5, h6⟩

/-- `Reversals.m4_exponent` with `ξ` an exponent that exists (`HasXiInv`) and the support lower bound
discharged; the upper bound `ξ ≤ log 2` (`thm:expceiling`) remains a hypothesis. -/
theorem m4_exponent' (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) {ξ : ℝ} (hξ : HasXiInv Ceilings.M4v ξ)
    (hhi : ξ ≤ Real.log 2) :
    ξ = Real.log 2 ∧ CK Ceilings.M4v = Real.log (9 / 4) ∧ ξ < CK Ceilings.M4v ∧
      CK Ceilings.M4v - ξ = Real.log (9 / 8) ∧
      0.1452 < 1 - ξ / CK Ceilings.M4v ∧ 1 - ξ / CK Ceilings.M4v < 0.1453 :=
  RealRep3Discharge.m4_exponent' h49 ξ
    (negLog_FC_le_of_hasXiInv Ceilings.nsq_M4v (by rw [RealRep3Discharge.FCΘ_M4v_eq']; norm_num) hξ) hhi

/-- **`cor:calgeom-spin1extensive` (a), exponent**: `ξ_inv(M₄^{⊗(m+1)}) = (m+1) log 2` and the gap to
`C_K` is `(m+1) log (9/8)`, given `F_K(M₄) ≤ 4/9` and the tensorised converse
`ξ̄_inv(M₄^{⊗(m+1)}) ≤ (m+1) log 2` (`P_⊗ ≥ ½ ∏ P_i` and `thm:expceiling`; not formalised). -/
theorem blocks_xi_inv' (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) (m : ℕ)
    (hhi : XiBarLE (Ceilings.M4pow m) ((m + 1) * Real.log 2)) :
    HasXiInv (Ceilings.M4pow m) ((m + 1) * Real.log 2) ∧
      CK (Ceilings.M4pow m) - (m + 1) * Real.log 2 = (m + 1) * Real.log (9 / 8) := by
  obtain ⟨hc, hw, hd⟩ := RealRep3Discharge.blocks_gap' h49 m
  have hpos : 0 < Ceilings.FCΘ (Ceilings.M4pow m) := by
    rw [RealRep3Discharge.FCΘ_M4pow_eq_half_pow']; positivity
  refine ⟨hasXiInv_of_xiBarLE (Ceilings.nsq_M4pow m) hpos hw hhi, ?_⟩
  rw [← hw]; exact hd

/-- `Reversals.blocks_exponent` with the support lower bound discharged. -/
theorem blocks_exponent' (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) (m : ℕ) {ξ : ℝ}
    (hξ : HasXiInv (Ceilings.M4pow m) ξ) (hhi : ξ ≤ (m + 1) * Real.log 2) :
    ξ = (m + 1) * Real.log 2 ∧ CK (Ceilings.M4pow m) - ξ = (m + 1) * Real.log (9 / 8) := by
  have hpos : 0 < Ceilings.FCΘ (Ceilings.M4pow m) := by
    rw [RealRep3Discharge.FCΘ_M4pow_eq_half_pow']; positivity
  exact RealRep3Discharge.blocks_exponent' h49 m ξ
    (negLog_FC_le_of_hasXiInv (Ceilings.nsq_M4pow m) hpos hξ) hhi

/-! ### Eight qubits -/

/-- **`cor:calgeom-spin1extensive` (b)**: `0 < s = cos 2θ < 1/8`, exchange bounds at `θ`, `F_K(M₄) ≤ 4/9`.
If `ξ_inv(M₄ ⊗ ψ_{U_θ}) = ξ` exists and obeys the tensorised converse `ξ ≤ log (4/(1+s))`, then
`ξ = log (4/(1+s)) < log 4 = ξ_inv(ψ₊ ⊗ ψ₊)` (the latter unconditional) and
`C_K(Ψ) = log (9/(2(1+s))) > log 4 = C_K(Φ)`: a strict reversal. -/
theorem eight_qubit_reversal_xi' (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4)
    (hK : Sharing.ExchangeIndepBound θ) (hC : Sharing.ExchangeIndepBoundC θ)
    (hs0 : 0 < Real.cos (2 * θ)) (hs1 : Real.cos (2 * θ) < 1 / 8) {ξ : ℝ}
    (hξ : HasXiInv (Reversals.Psi8 θ) ξ) (hhi : ξ ≤ Real.log (4 / (1 + Real.cos (2 * θ)))) :
    HasXiInv Reversals.Phi8 (Real.log 4) ∧ ξ = Real.log (4 / (1 + Real.cos (2 * θ))) ∧
      CK (Reversals.Psi8 θ) = Real.log (9 / (2 * (1 + Real.cos (2 * θ)))) ∧
      Reversals.StrictReversal (CK (Reversals.Psi8 θ)) ξ (CK Reversals.Phi8) (Real.log 4) := by
  obtain ⟨hrev, hck, hxi⟩ := PsiPlusKramers.eight_qubit_reversal'' h49 h0 h1 hK hC hs0 hs1
  obtain ⟨hp1, hp2⟩ := PsiPlusKramers.Phi8_values'
  obtain ⟨-, hfc, -, -⟩ := RealRep3Discharge.Psi8_values' h49 h0 h1 hK hC
  have hpos : 0 < Ceilings.FCΘ (Reversals.Psi8 θ) := by
    rw [hfc]; have : 0 < Real.cos (2 * θ) := hs0
    positivity
  have hlo := negLog_FC_le_of_hasXiInv (nsq_Psi8 θ) hpos hξ
  rw [hxi] at hlo
  have hξeq : ξ = Real.log (4 / (1 + Real.cos (2 * θ))) := le_antisymm hhi hlo
  rw [hp2, hxi] at hrev
  refine ⟨Phi8_xi_inv', hξeq, hck, ?_⟩
  rw [hξeq]; exact hrev

/-! ### Tensorisation, `thm:calgeom-tensorisation` -/

/-- **`thm:calgeom-tensorisation`, lower bound** (unconditional): for a product `ψ₁ ⊗ ψ₂` of unit states with
positive `F_C`, `-log F_C(ψ₁) - log F_C(ψ₂) ≤ ξ_inv(ψ₁ ⊗ ψ₂)` whenever the exponent exists. -/
theorem tens_negLog_le' {m n : ℕ} {ψ₁ : Ψ m} {ψ₂ : Ψ n} (h₁ : nsq ψ₁ = 1) (h₂ : nsq ψ₂ = 1)
    (p₁ : 0 < Ceilings.FCΘ ψ₁) (p₂ : 0 < Ceilings.FCΘ ψ₂) {ξ : ℝ} (hξ : HasXiInv (tens ψ₁ ψ₂) ξ) :
    -Real.log (Ceilings.FCΘ ψ₁) + -Real.log (Ceilings.FCΘ ψ₂) ≤ ξ := by
  have hn : nsq (tens ψ₁ ψ₂) = 1 := by rw [nsq_tens, h₁, h₂, one_mul]
  have hF := Ceilings.FCΘ_tens ψ₁ ψ₂ (by rw [h₁]; norm_num) (by rw [h₂]; norm_num)
  have := negLog_FC_le_of_hasXiInv hn (by rw [hF]; positivity) hξ
  rw [hF, Real.log_mul p₁.ne' p₂.ne'] at this
  linarith

/-- **`thm:calgeom-tensorisation`, additivity**: if `P_⊗(k) ≥ ½ P₁(k) P₂(k)` (the Helstrom product inequality,
not formalised, hypothesis `hP`), `ξ̄_inv(ψ_i) ≤ r_i` and `-log F_C(ψ_i) = r_i`, then `ξ_inv(ψ₁ ⊗ ψ₂) = r₁ + r₂`. -/
theorem tens_xi_inv' {m n : ℕ} {ψ₁ : Ψ m} {ψ₂ : Ψ n} (h₁ : nsq ψ₁ = 1) (h₂ : nsq ψ₂ = 1)
    (p₁ : 0 < Ceilings.FCΘ ψ₁) (p₂ : 0 < Ceilings.FCΘ ψ₂)
    (hP : ∀ k : ℕ, 1 / 2 * (Pe k ψ₁ * Pe k ψ₂) ≤ Pe k (tens ψ₁ ψ₂)) {r₁ r₂ : ℝ}
    (hr₁ : XiBarLE ψ₁ r₁) (hr₂ : XiBarLE ψ₂ r₂) (t₁ : -Real.log (Ceilings.FCΘ ψ₁) = r₁)
    (t₂ : -Real.log (Ceilings.FCΘ ψ₂) = r₂) : HasXiInv (tens ψ₁ ψ₂) (r₁ + r₂) := by
  have hn : nsq (tens ψ₁ ψ₂) = 1 := by rw [nsq_tens, h₁, h₂, one_mul]
  have hF := Ceilings.FCΘ_tens ψ₁ ψ₂ (by rw [h₁]; norm_num) (by rw [h₂]; norm_num)
  have hrate : Reversals.RateLE (fun k => Pe k (tens ψ₁ ψ₂)) (∑ i : Fin 2, ![r₁, r₂] i) := by
    refine Reversals.RateLE_prod_half (Finset.univ : Finset (Fin 2))
      (![fun k => Pe k ψ₁, fun k => Pe k ψ₂] : Fin 2 → ℕ → ℝ) (fun k => Pe k (tens ψ₁ ψ₂))
      ![r₁, r₂] ?_ ?_ ?_
    · intro i _ k
      fin_cases i
      · exact Pe_pos ψ₁ h₁ k
      · exact Pe_pos ψ₂ h₂ k
    · intro k
      simpa [Fin.prod_univ_two] using hP k
    · intro i _
      fin_cases i
      · exact (xiBarLE_iff_rateLE ψ₁ r₁).1 hr₁
      · exact (xiBarLE_iff_rateLE ψ₂ r₂).1 hr₂
  rw [Fin.sum_univ_two] at hrate
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hrate
  refine hasXiInv_of_xiBarLE hn (by rw [hF]; positivity) ?_ ((xiBarLE_iff_rateLE _ _).2 hrate)
  rw [hF, Real.log_mul p₁.ne' p₂.ne']
  linarith

end FormalResearch.FrameFree.XiInv
