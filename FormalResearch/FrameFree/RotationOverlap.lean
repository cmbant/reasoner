module

public import Mathlib
public import FormalResearch.NQubit.Foundations

/-!
# Rotation overlap on `n` qubits

On top of `FormalResearch.NQubit.Foundations` (`n`-qubit vectors `Ψ n`, local `SU(2)^n` rotations `rot u`, time
reversal `Θψ = ε^{⊗n} ψ̄`, Pauli average), this file defines the rotation overlap
`F_K(ψ,φ) = max_{u ∈ SU(2)^n} |⟨ψ|u φ⟩|²` (written `FK`, as a `sSup` with an explicit boundedness lemma);
`FKΘ ψ = F_K(ψ, Θψ)` and `CK ψ = -log F_K(ψ)`.

Proved here (all unconditional):

* `FKΘ_eq_FK_cj` (`F_K(ψ,Θψ) = F_K(ψ,ψ̄)` since `ε^{⊗n} ∈ K`), `FK_rot`;
* `le_FK`, `le_FK_one`, `le_FKΘ_one`, `rotSet_bddAbove` -- lower-bound witnesses;
* `two_pow_neg_le_FKΘ`, `CK_le` -- Theorem `thm:allnbounds`: `F_K(ψ) ≥ 2^{-n}` for unit `ψ`, hence
  `C_K ≤ n log 2` (via the Pauli average `pauli_average`);
* `FK_tens`, `FKΘ_tens`, `CK_tens` -- Prop `prop:mult` (rotation part), via `sSup_mul_of_independent`
  and the concatenation `tens` of states on `Fin m` and `Fin n` qubits.

The general `n`-qubit definitions and lemmas live in `FormalResearch.NQubit.Foundations`.
-/

@[expose] public section


open scoped ComplexConjugate Matrix BigOperators

namespace FormalResearch.FrameFree.NQubit

open FormalResearch.NQubit

/-- The set of overlaps `|⟨ψ|u φ⟩|²` over `u ∈ SU(2)^n`. -/
def rotSet {n : ℕ} (ψ φ : Ψ n) : Set ℝ :=
  {r | ∃ u : Fin n → Op1, (∀ i, SU2 (u i)) ∧ r = Complex.normSq (ip ψ (rot u φ))}

/-- Rotation overlap `F_K(ψ,φ) = max_{u ∈ K} |⟨ψ|u φ⟩|²`. -/
noncomputable def FK {n : ℕ} (ψ φ : Ψ n) : ℝ := sSup (rotSet ψ φ)

/-- `F_K(ψ) = F_K(ψ, Θψ)`. -/
noncomputable def FKΘ {n : ℕ} (ψ : Ψ n) : ℝ := FK ψ (Θ ψ)

/-- Chiral log-distance `C_K(ψ) = -log F_K(ψ)`. -/
noncomputable def CK {n : ℕ} (ψ : Ψ n) : ℝ := - Real.log (FKΘ ψ)

theorem rotSet_nonempty {n : ℕ} (ψ φ : Ψ n) : (rotSet ψ φ).Nonempty :=
  ⟨_, fun _ => 1, fun _ => SU2_one, rfl⟩

theorem rotSet_bddAbove {n : ℕ} (ψ φ : Ψ n) : BddAbove (rotSet ψ φ) := by
  refine ⟨nsq ψ * nsq φ, ?_⟩
  rintro r ⟨u, hu, rfl⟩
  have := normSq_ip_le ψ (rot u φ)
  rwa [nsq_rot u hu] at this

/-- Every `u ∈ SU(2)^n` gives a lower bound on `F_K`. -/
theorem le_FK {n : ℕ} (ψ φ : Ψ n) (u : Fin n → Op1) (hu : ∀ i, SU2 (u i)) :
    Complex.normSq (ip ψ (rot u φ)) ≤ FK ψ φ :=
  le_csSup (rotSet_bddAbove ψ φ) ⟨u, hu, rfl⟩

/-- `F_K(ψ,φ) ≥ |⟨ψ|φ⟩|²`. -/
theorem le_FK_one {n : ℕ} (ψ φ : Ψ n) : Complex.normSq (ip ψ φ) ≤ FK ψ φ := by
  have := le_FK ψ φ (fun _ => 1) (fun _ => SU2_one)
  rwa [rot_one] at this

/-- `F_K(ψ) ≥ |⟨ψ|Θψ⟩|²`. -/
theorem le_FKΘ_one {n : ℕ} (ψ : Ψ n) : Complex.normSq (ip ψ (Θ ψ)) ≤ FKΘ ψ :=
  le_FK_one ψ (Θ ψ)

theorem FK_le {n : ℕ} (ψ φ : Ψ n) : FK ψ φ ≤ nsq ψ * nsq φ := by
  refine csSup_le (rotSet_nonempty ψ φ) ?_
  rintro r ⟨u, hu, rfl⟩
  have := normSq_ip_le ψ (rot u φ)
  rwa [nsq_rot u hu] at this

theorem FK_nonneg {n : ℕ} (ψ φ : Ψ n) : 0 ≤ FK ψ φ :=
  (Complex.normSq_nonneg _).trans (le_FK_one ψ φ)

theorem rotSet_rot {n : ℕ} (ψ φ : Ψ n) (g : Fin n → Op1) (hg : ∀ i, SU2 (g i)) :
    rotSet ψ (rot g φ) = rotSet ψ φ := by
  ext r
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => u i * g i, fun i => SU2_mul (hu i) (hg i), by rw [rot_comp]⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨fun i => v i * (g i)ᴴ, fun i => SU2_mul (hv i) (SU2_adjoint (hg i)), ?_⟩
    rw [rot_comp]
    have : (fun i => v i * (g i)ᴴ * g i) = v := by
      funext i
      rw [Matrix.mul_assoc, (hg i).1, Matrix.mul_one]
    rw [this]

/-- `F_K` is invariant under rotating the second argument. -/
theorem FK_rot {n : ℕ} (ψ φ : Ψ n) (g : Fin n → Op1) (hg : ∀ i, SU2 (g i)) :
    FK ψ (rot g φ) = FK ψ φ := by
  unfold FK; rw [rotSet_rot ψ φ g hg]

/-- `F_K(ψ, Θψ) = F_K(ψ, ψ̄)`, since `ε^{⊗n} ∈ K`. -/
theorem FKΘ_eq_FK_cj {n : ℕ} (ψ : Ψ n) : FKΘ ψ = FK ψ (cj ψ) := by
  unfold FKΘ
  rw [Θ_eq_rot]
  exact FK_rot ψ (cj ψ) (fun _ => eps) (fun _ => SU2_eps)

/-- Every `u ∈ SU(2)^n` is applied equally to `Θψ`: `F_K(ψ,Θψ)` is the same in every frame. -/
theorem FK_Θ_rot {n : ℕ} (ψ : Ψ n) (u : Fin n → Op1) (hu : ∀ i, SU2 (u i)) :
    FK ψ (Θ (rot u ψ)) = FK ψ (rot u (Θ ψ)) := by
  rw [Θ_rot u hu]

/-! ### Theorem `thm:allnbounds`: the universal floor `F_K ≥ 2^{-n}` -/


/-- **Theorem `thm:allnbounds` (universal floor).** For a unit vector `ψ`, `F_K(ψ) ≥ 2^{-n}`;
more generally `F_K(ψ, φ) ≥ 2^{-n} ‖ψ‖²‖φ‖²`. -/
theorem le_FK_floor {n : ℕ} (ψ φ : Ψ n) :
    (2 : ℝ)⁻¹ ^ n * (nsq ψ * nsq φ) ≤ FK ψ φ := by
  have hsum := pauli_average ψ φ
  have hne : (Finset.univ : Finset (Fin n → Fin 4)).Nonempty := Finset.univ_nonempty
  have hcard : ((Finset.univ : Finset (Fin n → Fin 4)).card : ℝ) = 4 ^ n := by simp
  obtain ⟨a, -, ha⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => (2 : ℝ)⁻¹ ^ n * (nsq ψ * nsq φ))
    (g := fun a => Complex.normSq (ip ψ (rot (fun i => pauliSU (a i)) φ)))
    (by
      rw [hsum, Finset.sum_const, nsmul_eq_mul, hcard]
      have : (4 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ n = 2 ^ n := by
        rw [← mul_pow]; norm_num [show (4 : ℝ) = 2 * 2 by norm_num]
      calc (4 : ℝ) ^ n * ((2 : ℝ)⁻¹ ^ n * (nsq ψ * nsq φ))
          = ((4 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ n) * (nsq ψ * nsq φ) := by ring
        _ ≤ _ := by rw [this])
  exact ha.trans (le_FK ψ φ _ fun i => pauliSU_su2 (a i))

/-- **Theorem `thm:allnbounds`.** `F_K(ψ) ≥ 2^{-n}` for every unit vector. -/
theorem two_pow_neg_le_FKΘ {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) : (2 : ℝ)⁻¹ ^ n ≤ FKΘ ψ := by
  have := le_FK_floor ψ (Θ ψ)
  rwa [nsq_Θ, hψ, one_mul, mul_one] at this

theorem FKΘ_pos {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) : 0 < FKΘ ψ :=
  lt_of_lt_of_le (by positivity) (two_pow_neg_le_FKΘ ψ hψ)

/-- Consequence: `C_K(ψ) = -log F_K(ψ) ≤ n log 2`. -/
theorem CK_le {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) : CK ψ ≤ n * Real.log 2 := by
  have h := Real.log_le_log (by positivity) (two_pow_neg_le_FKΘ ψ hψ)
  rw [Real.log_pow, Real.log_inv] at h
  unfold CK
  linarith

/-! ### Proposition `prop:mult`: multiplicativity -/

/-- Multiplicativity of suprema of products over independent parameters. -/
theorem sSup_mul_of_independent {A B : Set ℝ} (hA : A.Nonempty) (hB : B.Nonempty)
    (hA0 : ∀ a ∈ A, 0 ≤ a) (hB0 : ∀ b ∈ B, 0 ≤ b) (hAb : BddAbove A) (hBb : BddAbove B) :
    sSup {r | ∃ a ∈ A, ∃ b ∈ B, r = a * b} = sSup A * sSup B := by
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  have hsA : 0 ≤ sSup A := (hA0 a₀ ha₀).trans (le_csSup hAb ha₀)
  have hsB : 0 ≤ sSup B := (hB0 b₀ hb₀).trans (le_csSup hBb hb₀)
  have hSb : BddAbove {r | ∃ a ∈ A, ∃ b ∈ B, r = a * b} := by
    refine ⟨sSup A * sSup B, ?_⟩
    rintro r ⟨a, ha, b, hb, rfl⟩
    exact mul_le_mul (le_csSup hAb ha) (le_csSup hBb hb) (hB0 b hb) hsA
  have hSne : {r | ∃ a ∈ A, ∃ b ∈ B, r = a * b}.Nonempty := ⟨_, a₀, ha₀, b₀, hb₀, rfl⟩
  have hM0 : 0 ≤ sSup {r | ∃ a ∈ A, ∃ b ∈ B, r = a * b} :=
    (mul_nonneg (hA0 a₀ ha₀) (hB0 b₀ hb₀)).trans (le_csSup hSb ⟨a₀, ha₀, b₀, hb₀, rfl⟩)
  apply le_antisymm
  · refine csSup_le hSne ?_
    rintro r ⟨a, ha, b, hb, rfl⟩
    exact mul_le_mul (le_csSup hAb ha) (le_csSup hBb hb) (hB0 b hb) hsA
  · set M := sSup {r | ∃ a ∈ A, ∃ b ∈ B, r = a * b} with hM
    have step1 : ∀ b ∈ B, sSup A * b ≤ M := by
      intro b hb
      rcases (hB0 b hb).eq_or_lt with h0 | hpos
      · rw [← h0]; simpa using hM0
      · have : sSup A ≤ M / b := csSup_le ⟨a₀, ha₀⟩ fun a ha =>
          (le_div_iff₀ hpos).2 (le_csSup hSb ⟨a, ha, b, hb, rfl⟩)
        exact (le_div_iff₀ hpos).1 this
    rcases hsA.eq_or_lt with h0 | hpos
    · rw [← h0]; simpa using hM0
    · have : sSup B ≤ M / sSup A := csSup_le ⟨b₀, hb₀⟩ fun b hb =>
        (le_div_iff₀ hpos).2 (by rw [mul_comm]; exact step1 b hb)
      exact (le_div_iff₀ hpos).1 this |>.trans_eq' (mul_comm _ _)

/-- The tensor product of states on the first `m` and last `n` of `m + n` qubits. -/
def tens {m n : ℕ} (ψ : Ψ m) (φ : Ψ n) : Ψ (m + n) :=
  fun x => ψ (fun i => x (Fin.castAdd n i)) * φ (fun j => x (Fin.natAdd m j))


theorem tens_append {m n : ℕ} (ψ : Ψ m) (φ : Ψ n) (a : Fin m → Fin 2) (b : Fin n → Fin 2) :
    tens ψ φ (Fin.append a b) = ψ a * φ b := by
  simp [tens]

theorem ip_tens {m n : ℕ} (ψ₁ φ₁ : Ψ m) (ψ₂ φ₂ : Ψ n) :
    ip (tens ψ₁ ψ₂) (tens φ₁ φ₂) = ip ψ₁ φ₁ * ip ψ₂ φ₂ := by
  simp only [ip]
  rw [sum_append, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [tens_append, map_mul]
  ring

theorem nsq_tens {m n : ℕ} (ψ : Ψ m) (φ : Ψ n) : nsq (tens ψ φ) = nsq ψ * nsq φ := by
  have := ip_tens ψ ψ φ φ
  rw [ip_self, ip_self, ip_self] at this
  exact_mod_cast this

theorem rot_tens {m n : ℕ} (u : Fin (m + n) → Op1) (φ₁ : Ψ m) (φ₂ : Ψ n) :
    rot u (tens φ₁ φ₂) =
      tens (rot (fun i => u (Fin.castAdd n i)) φ₁) (rot (fun j => u (Fin.natAdd m j)) φ₂) := by
  funext x
  simp only [rot, tens]
  rw [Finset.sum_mul_sum, sum_append]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  ring

theorem cj_tens {m n : ℕ} (ψ : Ψ m) (φ : Ψ n) : cj (tens ψ φ) = tens (cj ψ) (cj φ) := by
  funext x; simp [cj, tens]

/-- `Θ (ψ₁ ⊗ ψ₂) = Θψ₁ ⊗ Θψ₂`. -/
theorem Θ_tens {m n : ℕ} (ψ : Ψ m) (φ : Ψ n) : Θ (tens ψ φ) = tens (Θ ψ) (Θ φ) := by
  rw [Θ_eq_rot, cj_tens, rot_tens, Θ_eq_rot, Θ_eq_rot]

theorem rotSet_tens {m n : ℕ} (ψ₁ φ₁ : Ψ m) (ψ₂ φ₂ : Ψ n) :
    rotSet (tens ψ₁ ψ₂) (tens φ₁ φ₂) =
      {r | ∃ a ∈ rotSet ψ₁ φ₁, ∃ b ∈ rotSet ψ₂ φ₂, r = a * b} := by
  ext r
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨Complex.normSq (ip ψ₁ (rot (fun i => u (Fin.castAdd n i)) φ₁)),
      ⟨fun i => u (Fin.castAdd n i), fun i => hu _, rfl⟩,
      Complex.normSq (ip ψ₂ (rot (fun j => u (Fin.natAdd m j)) φ₂)),
      ⟨fun j => u (Fin.natAdd m j), fun j => hu _, rfl⟩, ?_⟩
    rw [rot_tens, ip_tens, Complex.normSq_mul]
  · rintro ⟨_, ⟨u₁, hu₁, rfl⟩, _, ⟨u₂, hu₂, rfl⟩, rfl⟩
    refine ⟨Fin.append u₁ u₂, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simpa using hu₁ i
      · simpa using hu₂ j
    · rw [rot_tens, ip_tens, Complex.normSq_mul]
      simp

/-- **Prop `prop:mult`** (rotation part): `F_K(ψ₁⊗ψ₂, φ₁⊗φ₂) = F_K(ψ₁,φ₁) F_K(ψ₂,φ₂)`. -/
theorem FK_tens {m n : ℕ} (ψ₁ φ₁ : Ψ m) (ψ₂ φ₂ : Ψ n) :
    FK (tens ψ₁ ψ₂) (tens φ₁ φ₂) = FK ψ₁ φ₁ * FK ψ₂ φ₂ := by
  unfold FK
  rw [rotSet_tens]
  refine sSup_mul_of_independent (rotSet_nonempty _ _) (rotSet_nonempty _ _) ?_ ?_
    (rotSet_bddAbove _ _) (rotSet_bddAbove _ _)
  · rintro _ ⟨u, -, rfl⟩; exact Complex.normSq_nonneg _
  · rintro _ ⟨u, -, rfl⟩; exact Complex.normSq_nonneg _

/-- **Prop `prop:mult`**: `F_K(ψ₁ ⊗ ψ₂) = F_K(ψ₁) F_K(ψ₂)` (with `ψ₁ ⊗ ψ₂` on disjoint spins). -/
theorem FKΘ_tens {m n : ℕ} (ψ₁ : Ψ m) (ψ₂ : Ψ n) :
    FKΘ (tens ψ₁ ψ₂) = FKΘ ψ₁ * FKΘ ψ₂ := by
  unfold FKΘ
  rw [Θ_tens, FK_tens]

/-- `C_K` is additive on products of unit vectors. -/
theorem CK_tens {m n : ℕ} (ψ₁ : Ψ m) (ψ₂ : Ψ n) (h₁ : nsq ψ₁ = 1) (h₂ : nsq ψ₂ = 1) :
    CK (tens ψ₁ ψ₂) = CK ψ₁ + CK ψ₂ := by
  unfold CK
  rw [FKΘ_tens, Real.log_mul (FKΘ_pos ψ₁ h₁).ne' (FKΘ_pos ψ₂ h₂).ne']
  ring

end FormalResearch.FrameFree.NQubit
