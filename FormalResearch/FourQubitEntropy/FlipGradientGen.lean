import FormalResearch.FourQubitEntropy.DualJet
import FormalResearch.FourQubitEntropy.Purity

/-!
# The spin-flip gradient identity, written generically

`H = F - (3/4) n W₁` is the polarization remainder of `thm:fqe-moment`, and `z̃ = ε^{⊗4} z̄` the
spin flip. Lemma `lem:fqe-flip-gradient` of `sextic_identity.tex` is the derivative of `H` along
the pencil `z + t z̃`. Here every ingredient is a generic expression (`RingOps`), so that the same
text can be evaluated in `ℂ` (statement), in `Dual ℂ` (derivative), and in `Dual SP` (the kernel
computes the normal form of the derivative).

* `H4gen z w = 4 F - 3 n W₁`;
* `H4dual z w`, the `ε`-part of `H4gen` at `(z + ε z̃, w + ε ẑ)` with `z̃ = ε^{⊗4} w`, `ẑ = ε^{⊗4} z`;
* `Ysite0`, `Ysum`: `Σ_i Σ_{idx} sgn(idx) R_i(idx) R_i(1-idx)` for the site tensors
  `R_i = 6 (V_i - 8U_i) = resTensor`, written with one representative of each slot class;
* `Spart`: `s (64 n² + 56 W₁ - 64 s s̄)` with `s = z^T ε^{⊗4} z`.

`flipGradDefect z w = 8 H4dual z w - (Rg z w + Rg w z)` is identically zero (`FlipGradient.lean`).
-/

open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

section Generic

variable {α : Type} [RingOps α]

/-- `4 F - 3 n W₁ = 4 (F - (3/4) n W₁)`. -/
def H4gen (z w : State α) : α :=
  lit 4 * Fgen z w - lit 3 * (normG z w * W1gen z w)

/-- The two ways `H4gen` is assembled from its blocks. `Fgen z w = 17 n P - 12 T - 12 n³`, with
`P = Σ_j tr R_{1j}²` and `T = Σ_j tr R_{1j}³` (`Pgen`, `T12gen + T13gen + T14gen`). -/
def Pgen (z w : State α) : α := tr2 (marg12 z w) + tr2 (marg13 z w) + tr2 (marg14 z w)
def T12gen (z w : State α) : α := tr3 (marg12 z w)
def T13gen (z w : State α) : α := tr3 (marg13 z w)
def T14gen (z w : State α) : α := tr3 (marg14 z w)

theorem H4gen_blocks (z w : State α) :
    H4gen z w = lit 4 * (lit 17 * normG z w * Pgen z w - lit 12 * (T12gen z w + T13gen z w + T14gen z w)
        - lit 12 * normG z w * normG z w * normG z w) - lit 3 * (normG z w * W1gen z w) := rfl

/-- `ε^{⊗4} w` as a state. -/
def ztilS (w : State α) : State α := fun a b c d => ztil w a b c d

/-- The two dual states of `H4dual`: `z + ε z̃` and `w + ε ẑ`. -/
def dualZ (z w : State α) : State (Dual α) := dualState z (ztilS w)
def dualW (z w : State α) : State (Dual α) := dualState w (ztilS z)

/-- The `ε`-part of `H4gen` at `(z + ε z̃, w + ε ẑ)`: the derivative of `4 H` along the pencil. -/
def H4dual (z w : State α) : α :=
  (H4gen (dualZ z w) (dualW z w)).b

/-- `Σ_{idx} sgn(idx) R(idx) R(1 - idx)` over the six legs `(x, y, t; o₁, o₂, o₃)` of the site-`0`
tensor `R = resTensor z w`, which is symmetric in `x, y, t`; one representative per slot class. -/
def Ysite0 (z w : State α) : α :=
  sum2 fun o1 => sum2 fun o2 => sum2 fun o3 =>
    lit (sgn o1 * sgn o2 * sgn o3) *
      (lit 2 * (resTensor z w 0 0 0 o1 o2 o3 * resTensor z w 1 1 1 (1 - o1) (1 - o2) (1 - o3))
        - lit 6 * (resTensor z w 0 0 1 o1 o2 o3 * resTensor z w 0 1 1 (1 - o1) (1 - o2) (1 - o3)))

/-- The sum over the four sites. -/
def Ysum (z w : State α) : α :=
  Ysite0 z w + Ysite0 (siteSwap 1 z) (siteSwap 1 w) + Ysite0 (siteSwap 2 z) (siteSwap 2 w)
    + Ysite0 (siteSwap 3 z) (siteSwap 3 w)

/-- `s (64 n² + 56 W₁ - 64 s s̄)`, `s = z^T ε^{⊗4} z`, `s̄ = w^T ε^{⊗4} w`. -/
def Spart (z w : State α) : α :=
  spinFlipForm z * (lit 64 * (normG z w * normG z w) + lit 56 * W1gen z w
    - lit 64 * (spinFlipForm z * spinFlipForm w))

/-- `8` times the complex right-hand side of the flip-gradient identity. -/
def Rg (z w : State α) : α := Ysum z w + Spart z w

/-- Identically zero: `8 · (ε-part of 4H) = Rg z w + Rg w z`. -/
def flipGradDefect (z w : State α) : α :=
  lit 8 * H4dual z w - (Rg z w + Rg w z)

end Generic

section Transfer

variable {α β : Type} [RingOps α] [RingOps β] {f : α → β}

theorem OpsHom.H4gen (hf : OpsHom f) (z w : State α) :
    f (H4gen z w) = H4gen (z.map f) (w.map f) := by
  simp only [FormalResearch.FourQubitEntropy.H4gen, hf.add', hf.sub', hf.mul', hf.lit', hf.Fgen,
    hf.normG, hf.W1gen]

theorem OpsHom.sgnlit (hf : OpsHom f) (k : ℤ) : f (lit k : α) = (lit k : β) := hf.map_ofInt k

theorem OpsHom.ztilS (hf : OpsHom f) (w : State α) :
    (ztilS w).map f = ztilS (w.map f) := by
  funext a b c d
  simp [State.map, FormalResearch.FourQubitEntropy.ztilS, hf.ztil]

theorem OpsHom.Ysite0 (hf : OpsHom f) (z w : State α) :
    f (Ysite0 z w) = Ysite0 (z.map f) (w.map f) := by
  simp only [FormalResearch.FourQubitEntropy.Ysite0, hf.sum2, hf.add', hf.sub', hf.mul', hf.lit',
    hf.resTensor]

theorem OpsHom.Ysum (hf : OpsHom f) (z w : State α) :
    f (Ysum z w) = Ysum (z.map f) (w.map f) := by
  simp only [FormalResearch.FourQubitEntropy.Ysum, hf.add', hf.Ysite0, ← hf.siteSwap]

theorem OpsHom.Spart (hf : OpsHom f) (z w : State α) :
    f (Spart z w) = Spart (z.map f) (w.map f) := by
  simp only [FormalResearch.FourQubitEntropy.Spart, hf.add', hf.sub', hf.mul', hf.lit', hf.normG,
    hf.W1gen, hf.spinFlipForm]

theorem OpsHom.Rg (hf : OpsHom f) (z w : State α) :
    f (Rg z w) = Rg (z.map f) (w.map f) := by
  simp only [FormalResearch.FourQubitEntropy.Rg, hf.add', hf.Ysum, hf.Spart]

theorem OpsHom.H4dual (hf : OpsHom f) (z w : State α) :
    f (H4dual z w) = H4dual (z.map f) (w.map f) := by
  have hd := (Dual.opsHom_map hf).H4gen (FormalResearch.FourQubitEntropy.dualZ z w)
    (FormalResearch.FourQubitEntropy.dualW z w)
  have e1 : (FormalResearch.FourQubitEntropy.dualZ z w).map (Dual.map f)
      = FormalResearch.FourQubitEntropy.dualZ (z.map f) (w.map f) := by
    funext a b c d
    have := congrFun (congrFun (congrFun (congrFun (hf.ztilS w) a) b) c) d
    simp only [State.map] at this
    simp [State.map, FormalResearch.FourQubitEntropy.dualZ, FormalResearch.FourQubitEntropy.dualW, dualState, Dual.map, this]
  have e2 : (FormalResearch.FourQubitEntropy.dualW z w).map (Dual.map f)
      = FormalResearch.FourQubitEntropy.dualW (z.map f) (w.map f) := by
    funext a b c d
    have := congrFun (congrFun (congrFun (congrFun (hf.ztilS z) a) b) c) d
    simp only [State.map] at this
    simp [State.map, FormalResearch.FourQubitEntropy.dualZ, FormalResearch.FourQubitEntropy.dualW, dualState, Dual.map, this]
  rw [e1, e2] at hd
  unfold FormalResearch.FourQubitEntropy.H4dual
  exact congrArg Dual.b hd

theorem OpsHom.flipGradDefect (hf : OpsHom f) (z w : State α) :
    f (flipGradDefect z w) = flipGradDefect (z.map f) (w.map f) := by
  simp only [FormalResearch.FourQubitEntropy.flipGradDefect, hf.add', hf.sub', hf.mul', hf.lit',
    hf.H4dual, hf.Rg]

end Transfer

end FormalResearch.FourQubitEntropy
