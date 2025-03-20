import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic

namespace IsNotZero

def p : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617
axiom p_prime : p.Prime
instance : Fact p.Prime := by rw [fact_iff]; exact p_prime

def Witness : Type := Fin 4 → ZMod p

-- Original circom:
/-
  template IsNotZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== in*inv;
    in === in*out;
  }

  component main = IsNotZero();
-/

def spec (w : Witness) : Prop :=
/-
  (in = 0 ∧ out = 0) ∨ (in ≠ 0 ∧ out = 1 ∧  in * inv = 1)
-/
  w 2 = 0 ∧ w 1 = 0  ∨ w 2 ≠ 0 ∧ w 1 = 1 ∧ w 2 * w 3 = 1

def circuit (w : Witness) : Prop :=
    (21888242871839275222246405745257275088548364400416034343698204186575808495616 * (w 2)) * (1 * (w 3)) = 21888242871839275222246405745257275088548364400416034343698204186575808495616 * (w 1) ∧
    (21888242871839275222246405745257275088548364400416034343698204186575808495616 * (w 2)) * (1 * (w 1)) = 21888242871839275222246405745257275088548364400416034343698204186575808495616 * (w 2)

example : ∀ w : Witness, w 0 = 1 → circuit w → spec w := by
  unfold circuit spec
  intros w w0_is_1
  have neg_lem_0 : (21888242871839275222246405745257275088548364400416034343698204186575808495616 : ZMod p) = -1 := by decide
  simp only [w0_is_1, one_mul, zero_add, neg_mul, neg_lem_0]
  intros h
  by_cases w2_is_0 : w 2 = 0
  · rw [w2_is_0, zero_mul] at h
    aesop
  · aesop

end IsNotZero
