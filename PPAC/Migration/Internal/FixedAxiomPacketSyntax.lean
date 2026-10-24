import PPAC.Migration.Internal.ObjectProofTreeEquation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatPacket

/-! 固定公理小标签的真实NatPacket叶包算术规格；不把它识别成结构树配数。 -/
namespace PPAC.Migration.Internal.FixedAxiomPacketSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
attribute [local irreducible] NaturalRecursionSyntax.matrix NaturalMultiplicationSyntax.product NaturalAdditionSyntax.sum SyntaxNumeralSyntax.numeral

def matrix {m} (tag : Nat) (w code : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 256 (env 0)).conj
    ((SyntaxNumeralSyntax.numeral tag (env 1)).conj
      ((NaturalMultiplicationSyntax.product w (env 0) (env 0) (env 2)).conj
        ((NaturalMultiplicationSyntax.product w (env 0) (env 2) (env 3)).conj
          ((NaturalMultiplicationSyntax.product w (env 0) (env 1) (env 4)).conj
            ((NaturalAdditionSyntax.sum w (env 3) (env 4) (env 5)).conj (successor code (env 5)))))))

def body {m} (tag : Nat) (w code : Fin m) : Formula (m+6) := matrix tag (old 6 w) (old 6 code) (slot 6)

def leaf {m} (tag : Nat) (w code : Fin m) : Formula m := existsMany 6 (body tag w code)

def existsLeaf {m} (tag : Nat) (w : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (leaf tag w.castSucc (Fin.last m)))

theorem matrix_rename {m l} (tag : Nat) (w code : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (matrix tag w code env).rename ρ = matrix tag (ρ w) (ρ code) (fun i => ρ (env i)) := by
  simp only [matrix, Formula.rename, SyntaxNumeralSyntax.numeral_rename, NaturalMultiplicationSyntax.product_rename,
    NaturalAdditionSyntax.sum_rename, successor_rename]

theorem body_lift {m l} (tag : Nat) (w code : Fin m) (ρ : Fin m → Fin l) :
    (body tag w code).rename (lift 6 ρ) = body tag (ρ w) (ρ code) := by
  simp only [body, matrix_rename, lift_old, lift_slot]

theorem leaf_rename {m l} (tag : Nat) (w code : Fin m) (ρ : Fin m → Fin l) :
    (leaf tag w code).rename ρ = leaf tag (ρ w) (ρ code) := by
  simp only [leaf, existsMany_rename, body_lift]

theorem existsLeaf_rename {m l} (tag : Nat) (w : Fin m) (ρ : Fin m → Fin l) :
    (existsLeaf tag w).rename ρ = existsLeaf tag (ρ w) := by
  simp only [existsLeaf, Formula.rename, leaf_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_leaf {m} {Γ : Context m} (tag : Nat) (w code : Fin m) (env : Fin 6 → Fin m)
    (hm : Derives Γ (matrix tag w code env)) : Derives Γ (leaf tag w code) := by
  apply HornBinderRules.intro_many 6 (body tag w code) env
  exact of_eq (by simp only [body, matrix_rename, assign_old, assign_slot]) hm

theorem intro_exists {m} {Γ : Context m} (tag : Nat) (w code : Fin m)
    (hn : Derives Γ (.mem code w)) (hc : Derives Γ (leaf tag w code)) : Derives Γ (existsLeaf tag w) := by
  apply Derives.exI code
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, leaf_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hn hc)

theorem varint_small (tag : Nat) (hk : tag < 128) : NatPacket.varint tag = [tag] := by
  rw [NatPacket.varint]
  exact if_pos hk

theorem packet_fold (base tag : Nat) :
    ([1,tag,0] : List Nat).foldr (fun byte rest => byte + base * rest) 1 =
      1 + base * (tag + base * (0 + base * 1)) := rfl

set_option maxHeartbeats 10000 in
theorem original_leaf_packet_raw (tag : Nat) (hk : tag < 128) :
    NatPacket.encode (NatPacket.leaf tag) = 1 + 256 * (tag + 256 * (0 + 256 * 1)) := by
  have hb : (1 :: NatPacket.treeTokens (NatPacket.leaf tag)).flatMap NatPacket.varint = [1,tag,0] := by
    simp only [NatPacket.leaf, NatPacket.treeTokens, List.length_nil, List.flatMap_cons, List.flatMap_nil,
      varint_small 1 (by decide), varint_small tag hk, varint_small 0 (by decide),
      List.cons_append, List.nil_append, List.append_nil]
  exact (congrArg (fun bytes : List Nat => bytes.foldr (fun byte rest => byte + 256 * rest) 1) hb).trans (packet_fold 256 tag)

set_option maxHeartbeats 10000 in
theorem packet_polynomial (base tag : Nat) :
    1 + base * (tag + base * (0 + base * 1)) = (base * (base * base) + base * tag) + 1 := by
  rw [Nat.mul_one, Nat.zero_add, Nat.mul_add]
  ac_rfl

set_option maxHeartbeats 10000 in
theorem original_leaf_packet_value (tag : Nat) (hk : tag < 128) :
    NatPacket.encode (NatPacket.leaf tag) = (256 * (256 * 256) + 256 * tag) + 1 := by
  exact (original_leaf_packet_raw tag hk).trans (packet_polynomial 256 tag)

end PPAC.Migration.Internal.FixedAxiomPacketSyntax
