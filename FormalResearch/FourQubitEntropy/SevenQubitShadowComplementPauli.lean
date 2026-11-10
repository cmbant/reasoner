module

public import FormalResearch.FourQubitEntropy.SevenQubitShadowComplementModel
public import FormalResearch.NQubit.TimeReversal.OddOverlap

/-!
# Concrete model for `prop:shadow-complement`: `J = ε^{⊗m} K` and the Pauli expansions of `ρ̄`

`QI/multiqubit_entanglement/seven_qubit_entanglement/shadow_equality_geometry.tex`, `prop:shadow-complement`.
Instantiates the abstract spin-flip model of `SevenQubitShadowComplementModel.lean` with qubits and proves the
Pauli-expansion inputs of the proposition from the shared `NQubit` library. For `ψ : Ψ n` and a distinguished
qubit `s`, put `S = univ.erase s` (the other `m = n - 1` qubits):

* `CfgSpace S = EuclideanSpace ℂ (CfgOn S)` and `spinFlipOp S = J_S = ε^{⊗S} K`, `(J v)(x) = ∑_y ε^{⊗S}(x,y) conj (v y)`;
  `isSpinFlip_spinFlipOp`: `J_S` is an antiunitary involution when `|S|` is even (`spinFlipOp_sq`: `J_S² = (-1)^{|S|}`).
* `branchVec ψ s a = u_a`, the branches of `ψ = |0⟩_s u₀ + |1⟩_s u₁`; `rdm_eq_sum`: the library's explicit partial
  trace `rdm ψ S` equals `∑_a |u_a⟩⟨u_a|` (so `ρ̄ = rho (branchVec ψ s)` in the abstract model).
* `trace_rdm_sq_eq`, `trace_rho_rho_eq`: `tr ρ̄² = ∑ |⟨u_a,u_b⟩|²` equals the purity `cutPurity ψ {s}` (`cutPurity_erase`:
  complementary reductions of a pure state have equal purity).
* `Rspin_eq`: the library's spin-flip overlap `R_{ρ̄} = tr(ρ̄ ρ̃)` (`ρ̃ = σ_y^{⊗m} ρ̄* σ_y^{⊗m}`, the matrix of
  `J ρ̄ J⁻¹`) equals `∑_{a,b} |T_{ab}|² = tr(ρ̄ J ρ̄ J⁻¹)`, `T_{ab} = ⟨u_a, J u_b⟩` (`Tm_eq`).
* `two_pow_mul_cutPurity_erase`: `2^m tr ρ̄² = ∑_j B_j` and `two_pow_mul_sum_Tm`: `2^m tr(ρ̄ J ρ̄ J⁻¹) = ∑_j (-1)^j B_j`,
  with `B_j = weightEnumExcl ψ s j`, from the library's `two_pow_mul_cutPurity` and `two_pow_mul_Rspin`
  (Pauli completeness and its signed form), regrouped by weight (`sum_wsupp_fiber`).

All proved; no hypotheses. The assembly into the boxed identities is `odd_weight_identities` in
`SevenQubitShadowComplement.lean`.
-/

@[expose] public section

open scoped ComplexConjugate BigOperators InnerProductSpace
open FormalResearch.NQubit.Pauli FormalResearch.NQubit.Reduced FormalResearch.NQubit.TimeReversal
open FormalResearch.NQubit (Ψ)

namespace FormalResearch.FourQubitEntropy.SevenQubitShadowComplement

variable {n : ℕ}

/-- The space of vectors of the qubits in `S`. -/
abbrev CfgSpace (S : Finset (Fin n)) := EuclideanSpace ℂ (CfgOn S)

theorem conj_epsOn (S : Finset (Fin n)) (x y : CfgOn S) : conj (epsOn S x y) = epsOn S x y := by
  unfold epsOn
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => conj_eps _ _

theorem eps_orth2 (a b : Fin 2) :
    ∑ c, FormalResearch.NQubit.eps c a * FormalResearch.NQubit.eps c b = if a = b then (1 : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;> simp [FormalResearch.NQubit.eps, Fin.sum_univ_two]

theorem eps_mul2 (a b : Fin 2) :
    ∑ c, FormalResearch.NQubit.eps a c * FormalResearch.NQubit.eps c b = (-1 : ℂ) * if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> simp [FormalResearch.NQubit.eps, Fin.sum_univ_two]

theorem epsOn_orth (S : Finset (Fin n)) (y z : CfgOn S) :
    ∑ x, epsOn S x y * epsOn S x z = if y = z then 1 else 0 := by
  unfold epsOn
  simp_rw [← Finset.prod_mul_distrib]
  rw [FormalResearch.NQubit.sum_prod_pi (fun i b => FormalResearch.NQubit.eps b (y i) *
    FormalResearch.NQubit.eps b (z i))]
  simp_rw [eps_orth2]
  rw [Finset.prod_boole]
  simp [funext_iff]

theorem epsOn_mul (S : Finset (Fin n)) (x z : CfgOn S) :
    ∑ y, epsOn S x y * epsOn S y z = (-1 : ℂ) ^ S.card * if x = z then 1 else 0 := by
  unfold epsOn
  simp_rw [← Finset.prod_mul_distrib]
  rw [FormalResearch.NQubit.sum_prod_pi (fun i b => FormalResearch.NQubit.eps (x i) b *
    FormalResearch.NQubit.eps b (z i))]
  simp_rw [eps_mul2]
  rw [Finset.prod_mul_distrib, Finset.prod_boole]
  simp [funext_iff]

/-- `J_S = ε^{⊗S} K` on the qubits in `S`. -/
noncomputable def spinFlipOp (S : Finset (Fin n)) : CfgSpace S →ₛₗ[starRingEnd ℂ] CfgSpace S where
  toFun v := WithLp.toLp 2 fun x => ∑ y, epsOn S x y * conj (v y)
  map_add' v w := by
    ext x
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext x
    simp [Finset.mul_sum, mul_left_comm]

theorem spinFlipOp_apply (S : Finset (Fin n)) (v : CfgSpace S) (x : CfgOn S) :
    spinFlipOp S v x = ∑ y, epsOn S x y * conj (v y) := rfl

theorem spinFlipOp_inner (S : Finset (Fin n)) (v w : CfgSpace S) :
    ⟪spinFlipOp S v, spinFlipOp S w⟫_ℂ = conj ⟪v, w⟫_ℂ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, spinFlipOp_apply, map_sum, map_mul,
    conj_epsOn, Complex.conj_conj]
  simp only [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  have : ∀ y, ∑ x, epsOn S x p * (starRingEnd ℂ) (w.ofLp p) * (epsOn S x y * v.ofLp y)
      = ((starRingEnd ℂ) (w.ofLp p) * v.ofLp y) * ∑ x, epsOn S x p * epsOn S x y := by
    intro y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  simp_rw [this, epsOn_orth]
  simp

/-- `J_S² = (-1)^{|S|}`. -/
theorem spinFlipOp_sq (S : Finset (Fin n)) (v : CfgSpace S) :
    spinFlipOp S (spinFlipOp S v) = ((-1 : ℂ) ^ S.card) • v := by
  ext x
  simp only [spinFlipOp_apply, map_sum, map_mul, conj_epsOn, Complex.conj_conj, PiLp.smul_apply,
    smul_eq_mul]
  have : ∀ y, epsOn S x y * ∑ z, epsOn S y z * v.ofLp z
      = ∑ z, (epsOn S x y * epsOn S y z) * v.ofLp z := by
    intro y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  simp_rw [this]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, epsOn_mul]
  simp

/-- `J_S` is an antiunitary involution when `|S|` is even (`J_m² = +1` for `m` even). -/
theorem isSpinFlip_spinFlipOp (S : Finset (Fin n)) (hS : Even S.card) :
    IsSpinFlip (spinFlipOp S) where
  inner_map := spinFlipOp_inner S
  invol v := by rw [spinFlipOp_sq, hS.neg_one_pow]; simp

/-! ### Reordering finite sums -/

section SumLemmas

variable {α β γ δ ι κ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ι]
  [Fintype κ]

theorem sum_out2 (f : α → β → ι → ℂ) :
    ∑ a, ∑ b, ∑ i, f a b i = ∑ i, ∑ a, ∑ b, f a b i :=
  (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

theorem sum_out3 (f : α → β → γ → ι → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ i, f a b c i = ∑ i, ∑ a, ∑ b, ∑ c, f a b c i :=
  (Finset.sum_congr rfl fun a _ => sum_out2 (f a)).trans Finset.sum_comm

theorem sum_out4 (f : α → β → γ → δ → ι → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, f a b c d i = ∑ i, ∑ a, ∑ b, ∑ c, ∑ d, f a b c d i :=
  (Finset.sum_congr rfl fun a _ => sum_out3 (f a)).trans Finset.sum_comm

theorem sum_out5 (f : α → β → γ → δ → ι → κ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ k, f a b c d i k = ∑ k, ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, f a b c d i k :=
  (Finset.sum_congr rfl fun a _ => sum_out4 (f a)).trans Finset.sum_comm

/-- Two inner sums moved to the front of four outer ones. -/
theorem sum_out_four_two (f : α → β → γ → δ → ι → κ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ k, f a b c d i k = ∑ k, ∑ i, ∑ a, ∑ b, ∑ c, ∑ d, f a b c d i k := by
  rw [sum_out5]
  exact Finset.sum_congr rfl fun k _ => sum_out4 (fun a b c d i => f a b c d i k)

theorem sum_swap22 (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d
      = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

end SumLemmas

/-! ### The branches `u_a` of the distinguished qubit and the reduced state `ρ̄` -/

/-- `Fin 2 ≃ CfgOff (univ.erase s)`: the single qubit `s` outside `univ.erase s` carries the value `a`. -/
def offEquiv (s : Fin n) : Fin 2 ≃ CfgOff (Finset.univ.erase s) where
  toFun a := fun _ => a
  invFun t := t ⟨s, by simp⟩
  left_inv _ := rfl
  right_inv t := by
    funext ⟨i, hi⟩
    have : i = s := by simpa using hi
    subst this
    rfl

theorem sum_off (s : Fin n) (F : CfgOff (Finset.univ.erase s) → ℂ) :
    ∑ t, F t = ∑ a : Fin 2, F (fun _ => a) :=
  (Equiv.sum_comp (offEquiv s) F).symm

/-- The branch `u_a` of `ψ = |0⟩_s u₀ + |1⟩_s u₁` on the qubits other than `s`. -/
noncomputable def branchVec (ψ : Ψ n) (s : Fin n) (a : Fin 2) : CfgSpace (Finset.univ.erase s) :=
  WithLp.toLp 2 fun x => ψ (glue (Finset.univ.erase s) x (fun _ => a))

theorem branchVec_apply (ψ : Ψ n) (s : Fin n) (a : Fin 2) (x : CfgOn (Finset.univ.erase s)) :
    branchVec ψ s a x = ψ (glue (Finset.univ.erase s) x (fun _ => a)) := rfl

/-- `ρ̄ = ∑_a |u_a⟩⟨u_a|`: the explicit partial trace is the sum of the rank-one projectors onto the branches. -/
theorem rdm_eq_sum (ψ : Ψ n) (s : Fin n) (x y : CfgOn (Finset.univ.erase s)) :
    rdm ψ (Finset.univ.erase s) x y = ∑ a, branchVec ψ s a x * conj (branchVec ψ s a y) := by
  unfold rdm
  rw [sum_off s (fun t => ψ (glue _ x t) * conj (ψ (glue _ y t)))]
  rfl

/-- `tr ρ̄² = ∑_{a,b} |⟨u_a, u_b⟩|²` for the explicit reduced matrix. -/
theorem trace_rdm_sq_eq (ψ : Ψ n) (s : Fin n) :
    ((rdm ψ (Finset.univ.erase s)) * (rdm ψ (Finset.univ.erase s))).trace =
      ∑ a, ∑ b, ((‖⟪branchVec ψ s a, branchVec ψ s b⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, rdm_eq_sum]
  simp only [Finset.sum_mul_sum]
  refine (sum_swap22 _).trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← inner_mul_inner_swap, mul_comm]
  simp only [PiLp.inner_apply, RCLike.inner_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- `T_{ab} = ⟨u_a, J u_b⟩ = ∑_{v,p} ū_a(v) ε(v,p) ū_b(p)`. -/
theorem Tm_eq (S : Finset (Fin n)) (z : Fin 2 → CfgSpace S) (a b : Fin 2) :
    Tm (spinFlipOp S) z a b = ∑ v, ∑ p, conj (z a v) * epsOn S v p * conj (z b p) := by
  simp only [Tm, PiLp.inner_apply, RCLike.inner_apply, spinFlipOp_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **`tr(ρ̄ J ρ̄ J⁻¹) = ∑_{a,b} |T_{ab}|²`, with `tr(ρ̄ J ρ̄ J⁻¹)` the explicit spin-flip overlap
`R_{ρ̄} = tr(ρ̄ ρ̃)` of `OddOverlap.lean`.** -/
theorem Rspin_eq (ψ : Ψ n) (s : Fin n) :
    Rspin ψ (Finset.univ.erase s) =
      ∑ a, ∑ b, ((‖Tm (spinFlipOp (Finset.univ.erase s)) (branchVec ψ s) a b‖ ^ 2 : ℝ) : ℂ) := by
  have step : ∀ (X : ℂ) (u v q p : CfgOn (Finset.univ.erase s)),
      spinFlipMat (Finset.univ.erase s) v p * X * spinFlipMat (Finset.univ.erase s) q u =
        X * (epsOn (Finset.univ.erase s) v p * epsOn (Finset.univ.erase s) u q) := by
    intro X u v q p
    calc _ = X * (spinFlipMat (Finset.univ.erase s) v p * spinFlipMat (Finset.univ.erase s) q u) := by
          ring
      _ = _ := by rw [spinFlip_mul]
  rw [Rspin_expand]
  simp only [step, sum_off s, ← branchVec_apply]
  refine (sum_out_four_two _).trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hT : ((‖Tm (spinFlipOp (Finset.univ.erase s)) (branchVec ψ s) a b‖ ^ 2 : ℝ) : ℂ) =
      (∑ u, ∑ q, branchVec ψ s a u * epsOn (Finset.univ.erase s) u q * branchVec ψ s b q) *
        ∑ v, ∑ p, conj (branchVec ψ s a v) * epsOn (Finset.univ.erase s) v p *
          conj (branchVec ψ s b p) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, mul_comm, Tm_eq]
    congr 1
    simp only [map_sum, map_mul, conj_epsOn, Complex.conj_conj]
  rw [hT]
  simp only [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
    Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  ring

/-! ### The Pauli expansions of `ρ̄` -/

/-- Regrouping a sum over the Pauli words supported in `S` by weight (`weight ≤ |S|`). -/
theorem sum_wsupp_fiber (S : Finset (Fin n)) (g : ℕ → ℝ) (f : (Fin n → Fin 4) → ℝ) :
    ∑ a ∈ wsupp S, g (pauliWeight a) * f a =
      ∑ j ∈ Finset.range (S.card + 1), g j *
        ∑ a ∈ (wsupp S).filter (fun a => pauliWeight a = j), f a := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := wsupp S) (t := Finset.range (S.card + 1))
    (g := pauliWeight)
    (fun a ha => Finset.mem_range.mpr (Nat.lt_succ_of_le (by
      rw [← card_pauliSupport]
      exact Finset.card_le_card (mem_wsupp_iff_pauliSupport.mp ha))))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.mp ha).2]

theorem card_erase_univ {m : ℕ} (s : Fin (m + 1)) : (Finset.univ.erase s).card = m := by simp

/-- `tr ρ̄² = tr ρ_s²`: complementary reductions of a pure state have the same purity. -/
theorem cutPurity_erase {m : ℕ} (ψ : Ψ (m + 1)) (s : Fin (m + 1)) :
    cutPurity ψ (Finset.univ.erase s) = cutPurity ψ {s} := by
  rw [← Finset.compl_singleton, cutPurity_compl]

/-- **Pauli completeness for `ρ̄`:** `2^m tr ρ̄² = ∑_j B_j` with `B_j = weightEnumExcl ψ s j`. -/
theorem two_pow_mul_cutPurity_erase {m : ℕ} (ψ : Ψ (m + 1)) (s : Fin (m + 1)) :
    (2 : ℝ) ^ m * cutPurity ψ (Finset.univ.erase s) =
      ∑ j ∈ Finset.range (m + 1), weightEnumExcl ψ s j := by
  have h := two_pow_mul_cutPurity ψ (Finset.univ.erase s)
  rw [card_erase_univ] at h
  rw [h]
  have := sum_wsupp_fiber (Finset.univ.erase s) (fun _ => 1) (pauliSq ψ)
  simp only [one_mul, card_erase_univ] at this
  rw [this]
  rfl

/-- **Signed Pauli expansion for `ρ̄`:** `2^m R_{ρ̄} = ∑_j (-1)^j B_j` for the spin-flip overlap
`R_{ρ̄} = tr(ρ̄ J ρ̄ J⁻¹) = ∑ |T_{ab}|²`. -/
theorem two_pow_mul_sum_Tm {m : ℕ} (ψ : Ψ (m + 1)) (s : Fin (m + 1)) :
    (2 : ℝ) ^ m * ∑ a, ∑ b, ‖Tm (spinFlipOp (Finset.univ.erase s)) (branchVec ψ s) a b‖ ^ 2 =
      ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j * weightEnumExcl ψ s j := by
  have h := two_pow_mul_Rspin ψ (Finset.univ.erase s)
  rw [Rspin_eq, card_erase_univ] at h
  have h2 : ((2 : ℝ) ^ m * ∑ a, ∑ b, ‖Tm (spinFlipOp (Finset.univ.erase s)) (branchVec ψ s) a b‖ ^ 2 : ℝ)
      = ((∑ a ∈ wsupp (Finset.univ.erase s), (-1 : ℝ) ^ pauliWeight a * pauliSq ψ a : ℝ) : ℂ) := by
    push_cast at h ⊢
    exact h
  have h3 := Complex.ofReal_injective h2
  rw [h3]
  have := sum_wsupp_fiber (Finset.univ.erase s) (fun j => (-1 : ℝ) ^ j) (pauliSq ψ)
  simp only [card_erase_univ] at this
  rw [this]
  rfl

/-- `Re tr ρ̄²` of the abstract operator `ρ̄ = ∑_a |u_a⟩⟨u_a|` is the purity `tr ρ_s²`. -/
theorem trace_rho_rho_eq {m : ℕ} (ψ : Ψ (m + 1)) (s : Fin (m + 1)) :
    (LinearMap.trace ℂ (CfgSpace (Finset.univ.erase s))
      (rho (branchVec ψ s) ∘ₗ rho (branchVec ψ s))).re = cutPurity ψ {s} := by
  rw [trace_rho_rho, ← cutPurity_erase, ← Complex.ofReal_re (cutPurity ψ _), cutPurity_eq_trace,
    trace_rdm_sq_eq]

end FormalResearch.FourQubitEntropy.SevenQubitShadowComplement

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitShadowComplement.isSpinFlip_spinFlipOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.SevenQubitShadowComplement.isSpinFlip_spinFlipOp

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitShadowComplement.two_pow_mul_cutPurity_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.SevenQubitShadowComplement.two_pow_mul_cutPurity_erase

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitShadowComplement.two_pow_mul_sum_Tm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.SevenQubitShadowComplement.two_pow_mul_sum_Tm
