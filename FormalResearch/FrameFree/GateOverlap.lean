import FormalResearch.FrameFree.WeylVertex

/-!
# The Weyl-vertex quantity of a two-qubit gate (gate law)

Paper P (`paper/long/app_d_gates_reversals.tex`, Lemma `lem:weylmax`, and the formula of Theorem
`thm:gatefk` in `sec5_gates.tex`).  For Cartan coordinates `c : Fin 3 → ℝ`, with the four tetrahedral
vectors `h_k ∈ {±1}³` of product `-1` (`Hm`), `λ_k = ∑_j h_kj c_j` and the Choi diagonal
`d_k = ½ e^{-iλ_k}` (`dgate`), we prove
`FKmag (dgate c) = ½ (1 + max_j |cos 4c_j|)` (`FKmag_gate`), together with the signed form
(`FKmag_gate_signs`) and the corollaries `δ = 1`, `δ = 0`, `C_K ≤ log 2`, and the exchange gate.

Proof architecture.  For `w = (σ, s)` one has `λ_k + λ_{σk} = (H v)_k` with `v = c + R_σ c`, where
`R_σ = ¼ Hᵀ P_σ H` is an integer signed permutation matrix in `W(D₃)` (`Rm`, `Rm_spec`, `cls_all`,
all by `decide +kernel`).  Every even sign vector is `± s_m` for one of four patterns (`pat`,
`sign_decomp`), and the key identities `∑_k pat_m,k e^{-i(Hv)_k}` = products of sines and cosines
(`pat_C0` ... `pat_S3`) give `|dᵀ w d|² = ∏ a_j + ∏ b_j` with `{a_j, b_j} = {cos² v_j, sin² v_j}`
(`N_eq`), which is `≤ max(a_k, b_k) = ½(1 + |cos 2 v_k|)` for every `k` (`flags_bound`).  It remains to
find `k` with `|cos 2 v_k| ≤ δ(c)`: `exists_small`, by the classification of `R_σ` into fixed point
(`clsF`), transposition (`clsP`) and 3-cycle (`clsC`) type and the trigonometric lemma `SS`.
The maximum is attained by the double transpositions (`low_attain`).
-/

open Finset Real

namespace FormalResearch.FrameFree

def Hm : Fin 4 → Fin 3 → ℤ := ![![1,1,-1],![1,-1,1],![-1,1,1],![-1,-1,-1]]
def Rm (σ : Equiv.Perm (Fin 4)) (j i : Fin 3) : ℤ := (∑ k, Hm k j * Hm (σ k) i) / 4

theorem Rm_spec : ∀ σ : Equiv.Perm (Fin 4), ∀ k : Fin 4, ∀ i : Fin 3,
    Hm (σ k) i = ∑ j, Hm k j * Rm σ j i := by decide +kernel

def clsF (σ : Equiv.Perm (Fin 4)) : Prop := ∃ k : Fin 3, ∀ i, Rm σ k i = if i = k then 1 else 0
def clsP (σ : Equiv.Perm (Fin 4)) : Prop := ∃ a b : Fin 3, a ≠ b ∧
  (∀ i, Rm σ a i = if i = b then 1 else 0) ∧ (∀ i, Rm σ b i = if i = a then -1 else 0)
def clsC (σ : Equiv.Perm (Fin 4)) : Prop := ∃ a b c : Fin 3, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
  ∃ e0 e1 e2 : Bool, sg e0 * sg e1 * sg e2 = 1 ∧
  (∀ i, Rm σ a i = if i = b then sg e0 else 0) ∧ (∀ i, Rm σ b i = if i = c then sg e1 else 0) ∧
  (∀ i, Rm σ c i = if i = a then sg e2 else 0)

instance (σ : Equiv.Perm (Fin 4)) : Decidable (clsF σ) := by unfold clsF; infer_instance
instance (σ : Equiv.Perm (Fin 4)) : Decidable (clsP σ) := by unfold clsP; infer_instance
instance (σ : Equiv.Perm (Fin 4)) : Decidable (clsC σ) := by unfold clsC; infer_instance

theorem cls_all : ∀ σ : Equiv.Perm (Fin 4), clsF σ ∨ clsP σ ∨ clsC σ := by decide +kernel

def pat : Fin 4 → Fin 4 → ℤ := ![![1,1,1,1],![-1,1,1,-1],![1,-1,1,-1],![1,1,-1,-1]]

theorem sign_decomp : ∀ s : Fin 4 → Bool, ∏ k, sg (s k) = 1 →
    ∃ g : Bool, ∃ q : Fin 4, ∀ k, sg (s k) = sg g * pat q k := by decide +kernel

theorem SS (X Y : ℝ) (h : 0 ≤ sin (2*X) * sin (2*Y)) :
    |cos (X+Y)| ≤ max |cos (2*X)| |cos (2*Y)| := by
  by_contra hcon
  rw [not_le] at hcon
  set M := max |cos (2*X)| |cos (2*Y)| with hM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (le_max_left _ _)
  have hα : |cos (2*X)| ≤ M := le_max_left _ _
  have hβ : |cos (2*Y)| ≤ M := le_max_right _ _
  have ha2 : M * M < cos (X+Y) * cos (X+Y) := by
    have := mul_self_lt_mul_self hM0 hcon
    rwa [abs_mul_abs_self] at this
  have hα2 : cos (2*X) * cos (2*X) ≤ M * M := by
    have := mul_self_le_mul_self (abs_nonneg _) hα
    rwa [abs_mul_abs_self] at this
  have hβ2 : cos (2*Y) * cos (2*Y) ≤ M * M := by
    have := mul_self_le_mul_self (abs_nonneg _) hβ
    rwa [abs_mul_abs_self] at this
  have hp := sin_sq_add_cos_sq X
  have hr := sin_sq_add_cos_sq Y
  rw [sin_two_mul] at h
  rw [sin_two_mul] at h
  rw [cos_two_mul'] at hα2 hβ2
  rw [cos_add] at ha2
  set p := cos X
  set q := sin X
  set r := cos Y
  set s := sin Y
  have hpqrs : 0 ≤ p*q*r*s := by nlinarith
  have hU1 : (p*s+q*r)^2 < 4*(p*q)^2 := by nlinarith
  have hU2 : (p*s+q*r)^2 < 4*(r*s)^2 := by nlinarith
  have hU0 : 0 ≤ (p*s+q*r)^2 := sq_nonneg _
  have hU3 : 4*(p*q*r*s) ≤ (p*s+q*r)^2 := by nlinarith [sq_nonneg (p*s-q*r)]
  have h4 := mul_self_lt_mul_self hU0 (lt_of_lt_of_le hU1 le_rfl)
  have h5 : (p*s+q*r)^2 * (p*s+q*r)^2 < 4*(p*q)^2 * (4*(r*s)^2) :=
    mul_lt_mul'' hU1 hU2 hU0 hU0
  have h6 : (4*(p*q*r*s)) * (4*(p*q*r*s)) ≤ (p*s+q*r)^2 * (p*s+q*r)^2 :=
    mul_self_le_mul_self (by positivity) hU3
  nlinarith


theorem ss' (Y1 Y2 e : ℝ) (he : e = 1 ∨ e = -1) (h : 0 ≤ e * sin (2*Y1) * sin (2*Y2)) :
    |cos (Y1 + e*Y2)| ≤ max |cos (2*Y1)| |cos (2*Y2)| := by
  rcases he with rfl | rfl
  · simpa using SS Y1 Y2 (by simpa using h)
  · have := SS Y1 (-Y2) (by rw [mul_neg, sin_neg]; nlinarith)
    simpa [sub_eq_add_neg, cos_neg, mul_neg] using this

/-- the constant `δ(c) = max_j |cos 4 c_j|` -/
noncomputable def δg (c : Fin 3 → ℝ) : ℝ := max (max |cos (4*c 0)| |cos (4*c 1)|) |cos (4*c 2)|

theorem le_δg (c : Fin 3 → ℝ) (k : Fin 3) : |cos (2*(2*c k))| ≤ δg c := by
  have : 2*(2*c k) = 4*c k := by ring
  rw [this]
  fin_cases k <;> simp [δg]

theorem sg_real (e : Bool) : ((sg e : ℤ) : ℝ) = 1 ∨ ((sg e : ℤ) : ℝ) = -1 := by
  cases e <;> simp [sg]

noncomputable def vv (σ : Equiv.Perm (Fin 4)) (c : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  c j + ∑ i, (Rm σ j i : ℝ) * c i

theorem sum_row (r : Fin 3 → ℤ) (b : Fin 3) (e : ℤ) (h : ∀ i, r i = if i = b then e else 0)
    (c : Fin 3 → ℝ) : ∑ i, (r i : ℝ) * c i = e * c b := by
  have : ∀ i, (r i : ℝ) * c i = if i = b then (e : ℝ) * c b else 0 := by
    intro i; rw [h i]; by_cases hi : i = b <;> simp [hi]
  simp [this]

theorem exists_small (σ : Equiv.Perm (Fin 4)) (c : Fin 3 → ℝ) : ∃ k : Fin 3, |cos (2 * vv σ c k)| ≤ δg c := by
  rcases cls_all σ with ⟨k, hk⟩ | ⟨a, b, hab, ha, hb⟩ | ⟨a, b, d, hab, hbd, had, e0, e1, e2, hprod, ha, hb, hd⟩
  · refine ⟨k, ?_⟩
    have := sum_row _ k 1 hk c
    unfold vv; rw [this]
    have h2 := le_δg c k
    convert h2 using 3; push_cast; ring
  · have hA := sum_row _ b 1 ha c
    have hB := sum_row _ a (-1) hb c
    have sa : vv σ c a = c a + c b := by unfold vv; rw [hA]; push_cast; ring
    have sb : vv σ c b = c b - c a := by unfold vv; rw [hB]; push_cast; ring
    by_cases hs : 0 ≤ sin (2*(2*c a)) * sin (2*(2*c b))
    · refine ⟨a, ?_⟩
      have := ss' (2*c a) (2*c b) 1 (Or.inl rfl) (by simpa using hs)
      rw [sa]
      have e : 2 * (c a + c b) = 2*c a + 1 * (2*c b) := by ring
      rw [e]
      exact le_trans this (max_le (le_δg c a) (le_δg c b))
    · refine ⟨b, ?_⟩
      have := ss' (2*c b) (2*c a) (-1) (Or.inr rfl) (by nlinarith)
      rw [sb]
      have e : 2 * (c b - c a) = 2*c b + (-1) * (2*c a) := by ring
      rw [e]
      exact le_trans this (max_le (le_δg c b) (le_δg c a))
  · have hA := sum_row _ b _ ha c
    have hB := sum_row _ d _ hb c
    have hD := sum_row _ a _ hd c
    have sa : 2 * vv σ c a = 2*c a + (sg e0 : ℝ) * (2 * c b) := by unfold vv; rw [hA]; ring
    have sb : 2 * vv σ c b = 2*c b + (sg e1 : ℝ) * (2 * c d) := by unfold vv; rw [hB]; ring
    have sd : 2 * vv σ c d = 2*c d + (sg e2 : ℝ) * (2 * c a) := by unfold vv; rw [hD]; ring
    have hp : (sg e0 : ℝ) * sg e1 * sg e2 = 1 := by exact_mod_cast hprod
    set Sa := sin (2*(2*c a))
    set Sb := sin (2*(2*c b))
    set Sd := sin (2*(2*c d))
    by_cases t1 : 0 ≤ (sg e0 : ℝ) * Sa * Sb
    · refine ⟨a, ?_⟩
      rw [sa]
      exact le_trans (ss' _ _ _ (sg_real e0) t1) (max_le (le_δg c a) (le_δg c b))
    by_cases t2 : 0 ≤ (sg e1 : ℝ) * Sb * Sd
    · refine ⟨b, ?_⟩
      rw [sb]
      exact le_trans (ss' _ _ _ (sg_real e1) t2) (max_le (le_δg c b) (le_δg c d))
    by_cases t3 : 0 ≤ (sg e2 : ℝ) * Sd * Sa
    · refine ⟨d, ?_⟩
      rw [sd]
      exact le_trans (ss' _ _ _ (sg_real e2) t3) (max_le (le_δg c d) (le_δg c a))
    exfalso
    push Not at t1 t2 t3
    have h12 := mul_pos_of_neg_of_neg t1 t2
    have h123 := mul_neg_of_pos_of_neg h12 t3
    have : ((sg e0 : ℝ) * Sa * Sb) * ((sg e1 : ℝ) * Sb * Sd) * ((sg e2 : ℝ) * Sd * Sa)
        = ((sg e0 : ℝ) * sg e1 * sg e2) * (Sa*Sb*Sd)^2 := by ring
    rw [this, hp] at h123
    nlinarith [sq_nonneg (Sa*Sb*Sd)]


/-- the four phases `(H v)_k` -/
noncomputable def phi (v : Fin 3 → ℝ) (k : Fin 4) : ℝ := ∑ j, (Hm k j : ℝ) * v j

theorem pat_C0 (v : Fin 3 → ℝ) : ∑ i, (pat 0 i : ℝ) * cos (phi v i) = 4 * (cos (v 0) * cos (v 1) * cos (v 2)) := by
  simp [pat, phi, Hm, Fin.sum_univ_four, Fin.sum_univ_three, cos_add, sin_add]
  ring

theorem pat_S0 (v : Fin 3 → ℝ) : ∑ i, (pat 0 i : ℝ) * sin (phi v i) = 4 * (sin (v 0) * sin (v 1) * sin (v 2)) := by
  simp [pat, phi, Hm, Fin.sum_univ_four, Fin.sum_univ_three, cos_add, sin_add]
  ring
theorem pat_C1 (v : Fin 3 → ℝ) : ∑ i, (pat 1 i : ℝ) * cos (phi v i) = 4 * (sin (v 0) * sin (v 1) * cos (v 2)) := by
  simp [pat, phi, Hm, Fin.sum_univ_four, Fin.sum_univ_three, cos_add, sin_add]
  ring
theorem pat_S1 (v : Fin 3 → ℝ) : ∑ i, (pat 1 i : ℝ) * sin (phi v i) = 4 * (cos (v 0) * cos (v 1) * sin (v 2)) := by
  simp [pat, phi, Hm, Fin.sum_univ_four, Fin.sum_univ_three, cos_add, sin_add]
  ring
theorem pat_C2 (v : Fin 3 → ℝ) : ∑ i, (pat 2 i : ℝ) * cos (phi v i) = 4 * (sin (v 0) * cos (v 1) * sin (v 2)) := by
  simp [pat, phi, Hm, Fin.sum_univ_four, Fin.sum_univ_three, cos_add, sin_add]
  ring
theorem pat_S2 (v : Fin 3 → ℝ) : ∑ i, (pat 2 i : ℝ) * sin (phi v i) = 4 * (cos (v 0) * sin (v 1) * cos (v 2)) := by
  simp [pat, phi, Hm, Fin.sum_univ_four, Fin.sum_univ_three, cos_add, sin_add]
  ring
theorem pat_C3 (v : Fin 3 → ℝ) : ∑ i, (pat 3 i : ℝ) * cos (phi v i) = 4 * (cos (v 0) * sin (v 1) * sin (v 2)) := by
  simp [pat, phi, Hm, Fin.sum_univ_four, Fin.sum_univ_three, cos_add, sin_add]
  ring
theorem pat_S3 (v : Fin 3 → ℝ) : ∑ i, (pat 3 i : ℝ) * sin (phi v i) = 4 * (sin (v 0) * cos (v 1) * cos (v 2)) := by
  simp [pat, phi, Hm, Fin.sum_univ_four, Fin.sum_univ_three, cos_add, sin_add]
  ring

def fl : Fin 4 → Fin 3 → Bool :=
  ![![false,false,false],![true,true,false],![true,false,true],![false,true,true]]

noncomputable def Aq (x : ℝ) (f : Bool) : ℝ := if f then sin x ^ 2 else cos x ^ 2
noncomputable def Bq (x : ℝ) (f : Bool) : ℝ := if f then cos x ^ 2 else sin x ^ 2

theorem N_eq (q : Fin 4) (v : Fin 3 → ℝ) :
    ((∑ i, (pat q i : ℝ) * cos (phi v i)) ^ 2 + (∑ i, (pat q i : ℝ) * sin (phi v i)) ^ 2) / 16 =
      ∏ j, Aq (v j) (fl q j) + ∏ j, Bq (v j) (fl q j) := by
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by fin_cases q <;> simp
  rcases hq with rfl | rfl | rfl | rfl
  · rw [pat_C0, pat_S0]
    simp [fl, Aq, Bq, Fin.prod_univ_three]; ring
  · rw [pat_C1, pat_S1]
    simp [fl, Aq, Bq, Fin.prod_univ_three]; ring
  · rw [pat_C2, pat_S2]
    simp [fl, Aq, Bq, Fin.prod_univ_three]; ring
  · rw [pat_C3, pat_S3]
    simp [fl, Aq, Bq, Fin.prod_univ_three]; ring

theorem prod_le0 (a0 b0 a1 b1 a2 b2 : ℝ) (h0 : 0 ≤ a0) (_h0' : 0 ≤ b0) (h1 : 0 ≤ a1) (h1' : 0 ≤ b1)
    (h2 : 0 ≤ a2) (h2' : 0 ≤ b2) (s1 : a1 + b1 = 1) (s2 : a2 + b2 = 1) :
    a0 * a1 * a2 + b0 * b1 * b2 ≤ max a0 b0 := by
  have hq : a1 * a2 + b1 * b2 ≤ 1 := by
    have : b1 = 1 - a1 := by linarith
    have : b2 = 1 - a2 := by linarith
    subst_vars
    nlinarith [mul_nonneg h1 h2, mul_nonneg h1' h2']
  have hm0 : 0 ≤ max a0 b0 := le_trans h0 (le_max_left _ _)
  calc a0 * a1 * a2 + b0 * b1 * b2 = a0 * (a1 * a2) + b0 * (b1 * b2) := by ring
    _ ≤ max a0 b0 * (a1 * a2) + max a0 b0 * (b1 * b2) := by
        gcongr <;> first | exact le_max_left _ _ | exact le_max_right _ _
    _ = max a0 b0 * (a1 * a2 + b1 * b2) := by ring
    _ ≤ max a0 b0 * 1 := by gcongr
    _ = max a0 b0 := mul_one _

theorem max_Aq (x : ℝ) (f : Bool) : max (Aq x f) (Bq x f) = (1 + |cos (2 * x)|) / 2 := by
  have h := sin_sq_add_cos_sq x
  have h2 : cos (2 * x) = cos x ^ 2 - sin x ^ 2 := by rw [cos_two_mul]; nlinarith
  cases f
  · simp only [Aq, Bq, Bool.false_eq_true, ite_false]
    rw [h2]
    rcases le_total (sin x ^ 2) (cos x ^ 2) with h3 | h3
    · rw [max_eq_left h3, abs_of_nonneg (by linarith)]; linarith
    · rw [max_eq_right h3, abs_of_nonpos (by linarith)]; linarith
  · simp only [Aq, Bq, ite_true]
    rw [h2]
    rcases le_total (cos x ^ 2) (sin x ^ 2) with h3 | h3
    · rw [max_eq_left h3, abs_of_nonpos (by linarith)]; linarith
    · rw [max_eq_right h3, abs_of_nonneg (by linarith)]; linarith

theorem AB_sum (x : ℝ) (f : Bool) : Aq x f + Bq x f = 1 := by
  have h := sin_sq_add_cos_sq x
  cases f <;> simp [Aq, Bq]

theorem Aq_nonneg (x : ℝ) (f : Bool) : 0 ≤ Aq x f := by cases f <;> simp [Aq] <;> positivity
theorem Bq_nonneg (x : ℝ) (f : Bool) : 0 ≤ Bq x f := by cases f <;> simp [Bq] <;> positivity

theorem flags_bound (v : Fin 3 → ℝ) (f : Fin 3 → Bool) (k : Fin 3) :
    ∏ j, Aq (v j) (f j) + ∏ j, Bq (v j) (f j) ≤ (1 + |cos (2 * v k)|) / 2 := by
  rw [← max_Aq (v k) (f k)]
  have key := fun (a0 b0 a1 b1 a2 b2 : ℝ) h0 h0' h1 h1' h2 h2' s1 s2 =>
    prod_le0 a0 b0 a1 b1 a2 b2 h0 h0' h1 h1' h2 h2' s1 s2
  simp only [Fin.prod_univ_three]
  fin_cases k
  · exact key _ _ _ _ _ _ (Aq_nonneg _ _) (Bq_nonneg _ _) (Aq_nonneg _ _) (Bq_nonneg _ _)
      (Aq_nonneg _ _) (Bq_nonneg _ _) (AB_sum _ _) (AB_sum _ _)
  · have := key (Aq (v 1) (f 1)) (Bq (v 1) (f 1)) (Aq (v 0) (f 0)) (Bq (v 0) (f 0))
      (Aq (v 2) (f 2)) (Bq (v 2) (f 2)) (Aq_nonneg _ _) (Bq_nonneg _ _) (Aq_nonneg _ _) (Bq_nonneg _ _)
      (Aq_nonneg _ _) (Bq_nonneg _ _) (AB_sum _ _) (AB_sum _ _)
    simp only [Fin.mk_one, Fin.isValue]
    calc _ = Aq (v 1) (f 1) * Aq (v 0) (f 0) * Aq (v 2) (f 2) + Bq (v 1) (f 1) * Bq (v 0) (f 0) * Bq (v 2) (f 2) := by ring
      _ ≤ _ := this
  · have := key (Aq (v 2) (f 2)) (Bq (v 2) (f 2)) (Aq (v 0) (f 0)) (Bq (v 0) (f 0))
      (Aq (v 1) (f 1)) (Bq (v 1) (f 1)) (Aq_nonneg _ _) (Bq_nonneg _ _) (Aq_nonneg _ _) (Bq_nonneg _ _)
      (Aq_nonneg _ _) (Bq_nonneg _ _) (AB_sum _ _) (AB_sum _ _)
    calc _ = Aq (v 2) (f 2) * Aq (v 0) (f 0) * Aq (v 1) (f 1) + Bq (v 2) (f 2) * Bq (v 0) (f 0) * Bq (v 1) (f 1) := by ring
      _ ≤ _ := this

theorem pat_bound (q : Fin 4) (v : Fin 3 → ℝ) (k : Fin 3) :
    ((∑ i, (pat q i : ℝ) * cos (phi v i)) ^ 2 + (∑ i, (pat q i : ℝ) * sin (phi v i)) ^ 2) / 16 ≤
      (1 + |cos (2 * v k)|) / 2 := by
  rw [N_eq]; exact flags_bound v _ k


/-! ### The gate diagonal -/

/-- `λ_k = ∑_j h_kj c_j` for Cartan coordinates `c`. -/
noncomputable def lam (c : Fin 3 → ℝ) (k : Fin 4) : ℝ := ∑ j, (Hm k j : ℝ) * c j

/-- The magic diagonal `d_k = ½ e^{-iλ_k}` of the Choi state of `exp(i ∑ c_j σ_j⊗σ_j)`. -/
noncomputable def dgate (c : Fin 3 → ℝ) : Fin 4 → ℂ :=
  fun k => (1 / 2 : ℂ) * Complex.exp (((-(lam c k) : ℝ) : ℂ) * Complex.I)

theorem lam_add (σ : Equiv.Perm (Fin 4)) (c : Fin 3 → ℝ) (k : Fin 4) :
    lam c k + lam c (σ k) = phi (vv σ c) k := by
  have h : ∀ i, (Hm (σ k) i : ℝ) = ∑ j, (Hm k j : ℝ) * (Rm σ j i : ℝ) := by
    intro i; exact_mod_cast Rm_spec σ k i
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [Fin.sum_univ_three] at h0 h1 h2
  unfold lam phi vv
  simp only [Fin.sum_univ_three]
  linear_combination (c 0) * h0 + (c 1) * h1 + (c 2) * h2

theorem weylVal_gate (c : Fin 3 → ℝ) (w : SP) :
    weylVal (dgate c) w =
      (1 / 4 : ℂ) * ∑ k, (sg (w.2 k) : ℂ) * Complex.exp (((-(phi (vv w.1 c) k) : ℝ) : ℂ) * Complex.I) := by
  unfold weylVal dgate
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : Complex.exp (((-(lam c k) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((-(lam c (w.1 k)) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-(phi (vv w.1 c) k) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    rw [← lam_add w.1 c k]
    push_cast
    ring
  rw [← e]
  ring

theorem normSq_sum (a : Fin 4 → ℤ) (φ : Fin 4 → ℝ) :
    Complex.normSq (∑ k, (a k : ℂ) * Complex.exp (((-(φ k) : ℝ) : ℂ) * Complex.I)) =
      (∑ k, (a k : ℝ) * cos (φ k)) ^ 2 + (∑ k, (a k : ℝ) * sin (φ k)) ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, cos_neg, sin_neg]
  simp only [zero_mul, mul_neg, neg_zero, sub_zero, add_zero, Finset.sum_neg_distrib]
  ring

theorem normSq_weylVal_gate (c : Fin 3 → ℝ) (w : SP) :
    Complex.normSq (weylVal (dgate c) w) =
      ((∑ k, (sg (w.2 k) : ℝ) * cos (phi (vv w.1 c) k)) ^ 2 +
        (∑ k, (sg (w.2 k) : ℝ) * sin (phi (vv w.1 c) k)) ^ 2) / 16 := by
  rw [weylVal_gate, map_mul, normSq_sum]
  have : Complex.normSq (1 / 4 : ℂ) = 1 / 16 := by
    rw [Complex.normSq_apply]; norm_num
  rw [this]; ring

theorem weylVal_le (c : Fin 3 → ℝ) {w : SP} (hw : w ∈ weylSet) :
    Complex.normSq (weylVal (dgate c) w) ≤ (1 + δg c) / 2 := by
  have hw' : ∏ k, sg (w.2 k) = 1 := by simpa [weylSet] using hw
  obtain ⟨g, q, hq⟩ := sign_decomp w.2 hw'
  obtain ⟨k, hk⟩ := exists_small w.1 c
  rw [normSq_weylVal_gate]
  have hg : ((sg g : ℤ) : ℝ) ^ 2 = 1 := by
    rcases sg_real g with h | h <;> rw [h] <;> norm_num
  have e1 : ∀ f : Fin 4 → ℝ, ∑ i, (sg (w.2 i) : ℝ) * f i = (sg g : ℝ) * ∑ i, (pat q i : ℝ) * f i := by
    intro f
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hq i]; push_cast; ring
  rw [e1, e1]
  have h := pat_bound q (vv w.1 c) k
  calc _ = (((∑ i, (pat q i : ℝ) * cos (phi (vv w.1 c) i)) ^ 2 +
            (∑ i, (pat q i : ℝ) * sin (phi (vv w.1 c) i)) ^ 2) / 16) * ((sg g : ℝ) ^ 2) := by ring
    _ ≤ (1 + |cos (2 * vv w.1 c k)|) / 2 := by rw [hg, mul_one]; exact h
    _ ≤ _ := by linarith


/-! ### Attainment: the double transpositions -/

theorem normSq_low (c : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 4)) (s : Fin 4 → Bool) (A : ℝ)
    (ε : Fin 4 → ℤ) (hφ : ∀ k, phi (vv σ c) k = (ε k : ℝ) * A) (hε : ∀ k, ε k = 1 ∨ ε k = -1) :
    Complex.normSq (weylVal (dgate c) (σ, s)) =
      ((∑ k, (sg (s k) : ℝ)) ^ 2 * cos A ^ 2 + (∑ k, (sg (s k) : ℝ) * (ε k : ℝ)) ^ 2 * sin A ^ 2) / 16 := by
  rw [normSq_weylVal_gate]
  simp only [hφ]
  have hc : ∀ k, cos ((ε k : ℝ) * A) = cos A := by
    intro k; rcases hε k with h | h <;> rw [h] <;> simp [cos_neg]
  have hs : ∀ k, sin ((ε k : ℝ) * A) = (ε k : ℝ) * sin A := by
    intro k; rcases hε k with h | h <;> rw [h] <;> simp [sin_neg]
  simp only [hc, hs]
  have e1 : ∑ k, (sg (s k) : ℝ) * cos A = (∑ k, (sg (s k) : ℝ)) * cos A := by rw [Finset.sum_mul]
  have e2 : ∑ k, (sg (s k) : ℝ) * ((ε k : ℝ) * sin A) = (∑ k, (sg (s k) : ℝ) * (ε k : ℝ)) * sin A := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
  simp only [e1, e2]
  ring

/-- For each coordinate `j` there are two Weyl elements with `|dᵀ w d|² = cos² 2c_j` and `sin² 2c_j`. -/
theorem low_attain (c : Fin 3 → ℝ) (j : Fin 3) :
    ∃ w ∈ weylSet, Complex.normSq (weylVal (dgate c) w) = cos (2 * c j) ^ 2 ∧
    ∃ w' ∈ weylSet, Complex.normSq (weylVal (dgate c) w') = sin (2 * c j) ^ 2 := by
  fin_cases j
  · -- σ = (0 1)(2 3), phases (A, A, -A, -A)
    have hφ : ∀ k, phi (vv (Equiv.swap 0 1 * Equiv.swap 2 3) c) k = (((![1, 1, -1, -1] : Fin 4 → ℤ) k : ℤ) : ℝ) * (2 * c 0) := by
      intro k
      rw [← lam_add]
      fin_cases k <;> simp [lam, Hm, Fin.sum_univ_three, Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring
    have hε : ∀ k, (![1, 1, -1, -1] : Fin 4 → ℤ) k = 1 ∨ (![1, 1, -1, -1] : Fin 4 → ℤ) k = -1 := by
      intro k; fin_cases k <;> simp
    refine ⟨(Equiv.swap 0 1 * Equiv.swap 2 3, fun _ => false), by decide +kernel, ?_,
      (Equiv.swap 0 1 * Equiv.swap 2 3, ![false, false, true, true]), by decide +kernel, ?_⟩
    · rw [normSq_low c _ _ _ _ hφ hε]
      simp [Fin.sum_univ_four, sg]; ring
    · rw [normSq_low c _ _ _ _ hφ hε]
      simp [Fin.sum_univ_four, sg]; ring
  · -- σ = (0 2)(1 3), phases (A, -A, A, -A)
    have hφ : ∀ k, phi (vv (Equiv.swap 0 2 * Equiv.swap 1 3) c) k = (((![1, -1, 1, -1] : Fin 4 → ℤ) k : ℤ) : ℝ) * (2 * c 1) := by
      intro k
      rw [← lam_add]
      fin_cases k <;> simp [lam, Hm, Fin.sum_univ_three, Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring
    have hε : ∀ k, (![1, -1, 1, -1] : Fin 4 → ℤ) k = 1 ∨ (![1, -1, 1, -1] : Fin 4 → ℤ) k = -1 := by
      intro k; fin_cases k <;> simp
    refine ⟨(Equiv.swap 0 2 * Equiv.swap 1 3, fun _ => false), by decide +kernel, ?_,
      (Equiv.swap 0 2 * Equiv.swap 1 3, ![false, true, false, true]), by decide +kernel, ?_⟩
    · rw [normSq_low c _ _ _ _ hφ hε]
      simp [Fin.sum_univ_four, sg]; ring
    · rw [normSq_low c _ _ _ _ hφ hε]
      simp [Fin.sum_univ_four, sg]; ring
  · -- σ = (0 3)(1 2), phases (-A, A, A, -A)
    have hφ : ∀ k, phi (vv (Equiv.swap 0 3 * Equiv.swap 1 2) c) k = (((![-1, 1, 1, -1] : Fin 4 → ℤ) k : ℤ) : ℝ) * (2 * c 2) := by
      intro k
      rw [← lam_add]
      fin_cases k <;> simp [lam, Hm, Fin.sum_univ_three, Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring
    have hε : ∀ k, (![-1, 1, 1, -1] : Fin 4 → ℤ) k = 1 ∨ (![-1, 1, 1, -1] : Fin 4 → ℤ) k = -1 := by
      intro k; fin_cases k <;> simp
    refine ⟨(Equiv.swap 0 3 * Equiv.swap 1 2, fun _ => false), by decide +kernel, ?_,
      (Equiv.swap 0 3 * Equiv.swap 1 2, ![true, false, false, true]), by decide +kernel, ?_⟩
    · rw [normSq_low c _ _ _ _ hφ hε]
      simp [Fin.sum_univ_four, sg]; ring
    · rw [normSq_low c _ _ _ _ hφ hε]
      simp [Fin.sum_univ_four, sg]; ring


/-! ### The gate law -/

theorem FKmag_ge (c : Fin 3 → ℝ) (j : Fin 3) : (1 + |cos (4 * c j)|) / 2 ≤ FKmag (dgate c) := by
  obtain ⟨w, hw, h1, w', hw', h2⟩ := low_attain c j
  have e1 := le_FKmag (dgate c) hw
  have e2 := le_FKmag (dgate c) hw'
  rw [h1] at e1
  rw [h2] at e2
  have hm := max_Aq (2 * c j) false
  simp only [Aq, Bq, Bool.false_eq_true, ite_false] at hm
  have e : 2 * (2 * c j) = 4 * c j := by ring
  rw [e] at hm
  rw [← hm]
  exact max_le e1 e2

/-- **Gate law** (paper P, Lemma `lem:weylmax` and the formula of Theorem `thm:gatefk`): for the Choi
diagonal `d_k = ½ e^{-iλ_k}` of the two-qubit gate with Cartan coordinates `c`,
`F_K = ½ (1 + max_j |cos 4c_j|)`.  Proved. -/
theorem FKmag_gate (c : Fin 3 → ℝ) :
    FKmag (dgate c) =
      (1 + max (max |cos (4 * c 0)| |cos (4 * c 1)|) |cos (4 * c 2)|) / 2 := by
  apply le_antisymm
  · exact (FKmag_le_iff _ _).2 fun w hw => weylVal_le c hw
  · have h0 := FKmag_ge c 0
    have h1 := FKmag_ge c 1
    have h2 := FKmag_ge c 2
    have : max (max |cos (4 * c 0)| |cos (4 * c 1)|) |cos (4 * c 2)| ≤ 2 * FKmag (dgate c) - 1 :=
      max_le (max_le (by linarith) (by linarith)) (by linarith)
    linarith

/-- The same with the sign pattern `d_k = ½ ε_k e^{-iλ_k}`, `ε` with an even number of minus signs
(Proposition `prop:choi`). -/
theorem FKmag_gate_signs (ε : Fin 4 → Bool) (hε : ∏ k, sg (ε k) = 1) (c : Fin 3 → ℝ) :
    FKmag (fun k => (1 / 2 : ℂ) * (sg (ε k) : ℂ) * Complex.exp (((-(lam c k) : ℝ) : ℂ) * Complex.I)) =
      (1 + max (max |cos (4 * c 0)| |cos (4 * c 1)|) |cos (4 * c 2)|) / 2 := by
  have : (fun k => (1 / 2 : ℂ) * (sg (ε k) : ℂ) * Complex.exp (((-(lam c k) : ℝ) : ℂ) * Complex.I)) =
      signFlip ε (dgate c) := by
    funext k; simp only [signFlip, dgate]; ring
  rw [this, FKmag_signFlip ε hε, FKmag_gate]

/-! ### Corollaries -/

theorem abs_cos_le_δg (c : Fin 3 → ℝ) (j : Fin 3) : |cos (4 * c j)| ≤ δg c := by
  have := le_δg c j
  rwa [show 2 * (2 * c j) = 4 * c j by ring] at this

theorem δg_nonneg (c : Fin 3 → ℝ) : 0 ≤ δg c := le_trans (abs_nonneg _) (abs_cos_le_δg c 0)

theorem δg_le_one (c : Fin 3 → ℝ) : δg c ≤ 1 :=
  max_le (max_le (abs_cos_le_one _) (abs_cos_le_one _)) (abs_cos_le_one _)

theorem abs_cos_eq_one_iff_sin (y : ℝ) : |cos y| = 1 ↔ sin y = 0 := by
  have h := sin_sq_add_cos_sq y
  constructor
  · intro h1
    have : cos y ^ 2 = 1 := by rw [← sq_abs, h1]; norm_num
    have : sin y ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  · intro h1
    rw [h1] at h
    have : |cos y| ^ 2 = 1 := by rw [sq_abs]; linarith
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).1 this

theorem sin_four_eq_zero_iff (x : ℝ) : sin (4 * x) = 0 ↔ ∃ n : ℤ, x = n * (π / 4) := by
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [hn]; ring⟩

theorem cos_four_eq_zero_iff (x : ℝ) : cos (4 * x) = 0 ↔ ∃ n : ℤ, x = π / 8 + n * (π / 4) := by
  rw [Real.cos_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [hn]; ring⟩

/-- (i) `δ = 1` iff some Cartan coordinate lies in `(π/4)ℤ`. -/
theorem δg_eq_one_iff_sin (c : Fin 3 → ℝ) : δg c = 1 ↔ ∃ j, sin (4 * c j) = 0 := by
  constructor
  · intro h
    have : ∃ j, |cos (4 * c j)| = 1 := by
      unfold δg at h
      rcases max_choice (max |cos (4 * c 0)| |cos (4 * c 1)|) |cos (4 * c 2)| with h1 | h1
      · rw [h1] at h
        rcases max_choice |cos (4 * c 0)| |cos (4 * c 1)| with h2 | h2
        · exact ⟨0, by rw [← h, h2]⟩
        · exact ⟨1, by rw [← h, h2]⟩
      · exact ⟨2, by rw [← h, h1]⟩
    obtain ⟨j, hj⟩ := this
    exact ⟨j, (abs_cos_eq_one_iff_sin _).1 hj⟩
  · rintro ⟨j, hj⟩
    exact le_antisymm (δg_le_one c) (by rw [← (abs_cos_eq_one_iff_sin _).2 hj]; exact abs_cos_le_δg c j)

theorem δg_eq_one_iff (c : Fin 3 → ℝ) : δg c = 1 ↔ ∃ j, ∃ n : ℤ, c j = n * (π / 4) := by
  rw [δg_eq_one_iff_sin]
  exact exists_congr fun j => sin_four_eq_zero_iff _

/-- (ii) `δ = 0` iff every Cartan coordinate lies in `π/8 + (π/4)ℤ`. -/
theorem δg_eq_zero_iff_cos (c : Fin 3 → ℝ) : δg c = 0 ↔ ∀ j, cos (4 * c j) = 0 := by
  constructor
  · intro h j
    have h1 := abs_cos_le_δg c j
    rw [h] at h1
    exact abs_eq_zero.1 (le_antisymm h1 (abs_nonneg _))
  · intro h
    unfold δg
    simp [h 0, h 1, h 2]

theorem δg_eq_zero_iff (c : Fin 3 → ℝ) : δg c = 0 ↔ ∀ j, ∃ n : ℤ, c j = π / 8 + n * (π / 4) := by
  rw [δg_eq_zero_iff_cos]
  exact forall_congr' fun j => cos_four_eq_zero_iff _

/-- (iii) The Choi-state value `C_K = -log F_K = log (2/(1+δ)) ∈ [0, log 2]`. -/
theorem CK_gate (c : Fin 3 → ℝ) :
    -Real.log (FKmag (dgate c)) = Real.log (2 / (1 + δg c)) ∧
      Real.log (2 / (1 + δg c)) ≤ Real.log 2 ∧ 0 ≤ Real.log (2 / (1 + δg c)) := by
  have h0 := δg_nonneg c
  have h1 := δg_le_one c
  have hF : FKmag (dgate c) = (1 + δg c) / 2 := FKmag_gate c
  have hpos : 0 < 1 + δg c := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hF, ← Real.log_inv, inv_div]
  · exact Real.log_le_log (div_pos two_pos hpos) (by rw [div_le_iff₀ hpos]; linarith)
  · exact Real.log_nonneg (by rw [le_div_iff₀ hpos]; linarith)

/-- (iv) The exchange-type gates `c = (θ/2, θ/2, θ/2)`: `F_K = (1 + |cos 2θ|)/2`. -/
theorem FKmag_gate_exchange (θ : ℝ) :
    FKmag (dgate (fun _ => θ / 2)) = (1 + |cos (2 * θ)|) / 2 := by
  rw [FKmag_gate]
  have : 4 * (θ / 2) = 2 * θ := by ring
  simp [this]

/-- `θ = π/4` (the √SWAP-type point) has `F_K = 1/2`. -/
theorem FKmag_gate_exchange_quarter : FKmag (dgate (fun _ => (π / 4) / 2)) = 1 / 2 := by
  rw [FKmag_gate_exchange, show 2 * (π / 4) = π / 2 by ring, cos_pi_div_two]
  norm_num


end FormalResearch.FrameFree
