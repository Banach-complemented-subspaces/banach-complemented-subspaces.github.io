import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card

namespace ComplementedSubspace

/-- Samples in the finite four-point product frame. -/
def FrameIndex : ℕ → Type
  | 0 => Unit
  | k + 1 => Fin 4 × FrameIndex k

instance frameIndexFintype : (k : ℕ) → Fintype (FrameIndex k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 => @instFintypeProd (Fin 4) (FrameIndex k)
      inferInstance (frameIndexFintype k)

instance frameIndexDecidableEq (k : ℕ) : DecidableEq (FrameIndex k) := by
  induction k with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ k ih =>
    letI : DecidableEq (FrameIndex k) := ih
    exact inferInstanceAs (DecidableEq (Fin 4 × FrameIndex k))

instance frameIndexNonempty : (k : ℕ) → Nonempty (FrameIndex k)
  | 0 => inferInstanceAs (Nonempty Unit)
  | k + 1 => let ⟨s⟩ := frameIndexNonempty k; ⟨(0, s)⟩

theorem frameIndex_card (k : ℕ) : Fintype.card (FrameIndex k) = 4 ^ k := by
  induction k with
  | zero => exact Fintype.card_unit
  | succ k ih =>
    change Fintype.card (Fin 4 × FrameIndex k) = _
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ, Nat.mul_comm]

end ComplementedSubspace
