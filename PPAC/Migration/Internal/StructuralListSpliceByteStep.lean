import PPAC.Migration.Internal.StructuralListSpliceBytePoint

/-! The exact existing ByteList decomposition gives a genuine smaller actual tail code; its original membership in the Cons code authorizes the IH. -/
namespace PPAC.Migration.Internal.StructuralListSpliceByteStep
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax StructuralListSpliceByteSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem from_earlier_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n))
    (hn : Derives Γ (PacketByteInputSyntax.byteList w n))
    (ht : Derives Γ (PacketByteInputSyntax.byteList w t))
    (hs : Derives Γ (StructuralListSpliceSyntax.splice w n t a)) :
    Derives Γ (PacketByteInputSyntax.byteList w a) := by
  have hd := Derives.impE (.conjL (PacketByteInputLaws.actual_iff hZ w n hw)) hn
  apply Derives.disjE hd
  · exact StructuralListSpliceBytePoint.nil_point (ZFContext.add hZ _) _ _ _ _
      (add hw _) (.hyp (Or.inl rfl)) (add ht _) (add hs _)
  · let P := PacketByteInputRecursionSyntax.actualCons w n
    let R := PacketByteInputRecursionSyntax.actualBody w n
    let Δ := Context.add R (raisedContext 2 (Context.add P Γ))
    apply HornBinderRules.eliminate_many 2 R _ (.hyp (Or.inl rfl) : Derives (Context.add P Γ) P)
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ2 := HornBinderRules.zf_body 2 (ZFContext.add hZ P) R
    have lift2 {φ : Formula m} (hp : Derives Γ φ) : Derives Δ (φ.rename (old 2)) :=
      HornBinderRules.under_body 2 (add hp P) R
    have hw2 := of_eq (omega_rename w (old 2)) (lift2 hw)
    have hi2 := of_eq (earlier_rename w n (old 2)) (lift2 hi)
    have ht2 := of_eq (PacketByteInputSyntax.byteList_rename w t (old 2)) (lift2 ht)
    have hs2 := of_eq (StructuralListSpliceSyntax.splice_rename w n t a (old 2)) (lift2 hs)
    have hh := Derives.conjL (.conjR hR)
    have hx := Derives.conjR (.conjR hR)
    have hhN := PacketByteInputLaws.byte_natural hZ2 (old 2 w) (slot 2 0) hw2 hh
    have hxN := PacketByteInputLaws.natural (old 2 w) (slot 2 1) hx
    have hBelow := Derives.conjR (StructuralConsCore.components hZ2 (old 2 w) (slot 2 0) (slot 2 1) (old 2 n) hw2 hhN hxN (.conjL hR))
    have hSmall := earlier_at (old 2 w) (old 2 n) (slot 2 1) hi2 hxN hBelow
    exact of_eq (PacketByteInputSyntax.byteList_rename w a (old 2)).symm
      (StructuralListSpliceBytePoint.cons_point hZ2 (old 2 w) (slot 2 0) (slot 2 1) (old 2 n) (old 2 t) (old 2 a)
        hw2 hh hx (.conjL hR) hSmall ht2 hs2)

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  apply Derives.impI
  let N := PacketByteInputSyntax.byteList w n
  apply OriginalUniversalBlock.intro_many 2 (body w n)
  apply Derives.impI
  apply Derives.impI
  let T := PacketByteInputSyntax.byteList (old 2 w) (slot 2 0)
  let S := StructuralListSpliceSyntax.splice (old 2 w) (old 2 n) (slot 2 0) (slot 2 1)
  let Δ := Context.add S (Context.add T (raisedContext 2 (Context.add N Γ)))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (HornBinderRules.zf_many 2 (ZFContext.add hZ N)) T) S
  have lift2 {φ : Formula m} (hp : Derives Γ φ) : Derives Δ (φ.rename (old 2)) :=
    add (add (HornBinderRules.under_many 2 (add hp N)) T) S
  have hw2 := of_eq (omega_rename w (old 2)) (lift2 hw)
  have hi2 := of_eq (earlier_rename w n (old 2)) (lift2 hi)
  have hn2 : Derives Δ (PacketByteInputSyntax.byteList (old 2 w) (old 2 n)) :=
    of_eq (PacketByteInputSyntax.byteList_rename w n (old 2))
      (add (add (HornBinderRules.under_many 2 (.hyp (Or.inl rfl) : Derives (Context.add N Γ) N)) T) S)
  have hT : Derives Δ T := .hyp (Or.inr (Or.inl rfl))
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  exact from_earlier_point hZ2 (old 2 w) (old 2 n) (slot 2 0) (slot 2 1) hw2 hi2 hn2 hT hS

end PPAC.Migration.Internal.StructuralListSpliceByteStep
