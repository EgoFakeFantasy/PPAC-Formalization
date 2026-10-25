import PPAC.Migration.Internal.StructuralListSpliceSnocStep

/-! Full original code induction proves the singleton-splice Snoc contract for every actual internal prefix. -/
namespace PPAC.Migration.Internal.StructuralListSpliceSnoc
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax StructuralListSpliceSnocSyntax
open ReplacementPredicates (paramsUp)
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  apply OriginalUniversalBlock.intro_many 5 (body w n)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let A := Formula.mem (slot 5 0) (old 5 w)
  let N := StructuralListLengthSyntax.hasLength (old 5 w) (old 5 n) (slot 5 3)
  let S := PacketVarintCanonicalRecursionSyntax.singleton (old 5 w) (slot 5 0) (slot 5 1)
  let R := StructuralListSpliceSyntax.splice (old 5 w) (old 5 n) (slot 5 1) (slot 5 2)
  let E : Formula (m + 5) := successor (slot 5 4) (slot 5 3)
  let Δ := Context.add E (Context.add R (Context.add S (Context.add N (Context.add A (raisedContext 5 Γ)))))
  have hZ5 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (HornBinderRules.zf_many 5 hZ) A) N) S) R) E
  have lift {φ : Formula m} (hp : Derives Γ φ) : Derives Δ (φ.rename (old 5)) := add (add (add (add (add (HornBinderRules.under_many 5 hp) A) N) S) R) E
  have hw5 := of_eq (omega_rename w (old 5)) (lift hw)
  have hi5 := of_eq (earlier_rename w n (old 5)) (lift hi)
  have hA : Derives Δ A := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hN : Derives Δ N := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hS : Derives Δ S := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have hR : Derives Δ R := .hyp (Or.inr (Or.inl rfl))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact StructuralListSpliceSnocStep.from_earlier hZ5 (old 5 w) (old 5 n) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4) hw5 hi5 hA hN hS hR hE

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (BoundedInduction.progressive StructuralListSpliceSnocSyntax.matrix (fun _ : Fin 1 => w) w) := by
  simp only [BoundedInduction.progressive,BoundedInduction.below,StructuralListSpliceSnocSyntax.matrix_pred,paramsUp]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let I := earlier w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add M (Context.image Formula.raise Γ))
  have hZ1 := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) M) I
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise,omega_rename] using add (add (Derives.rename Fin.castSucc hw) M) I
  exact property_from_earlier hZ1 w.castSucc (Fin.last m) hw1 (.hyp (Or.inl rfl))

theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))) := by
  have hp := BoundedInduction.induction_on_set StructuralListSpliceSnocSyntax.matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ StructuralListSpliceSnocSyntax.matrix.neg) (ZFContext.arithmetic hZ).base.foundation (progressive hZ w hw)
  simpa only [BoundedInduction.holds,StructuralListSpliceSnocSyntax.matrix_pred,paramsUp] using hp

theorem at_splice {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h S r l L : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hn : Derives Γ (StructuralListLengthSyntax.hasLength w n l))
    (hS : Derives Γ (PacketVarintCanonicalRecursionSyntax.singleton w h S)) (hSp : Derives Γ (StructuralListSpliceSyntax.splice w n S r))
    (hL : Derives Γ (successor L l)) : Derives Γ (StructuralListReverseConsContract.snoc w n l L h r) := by
  have hi : Derives Γ ((Formula.mem n w).imp (property w n)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE n (all_properties hZ w hw))
  have hp := Derives.impE hi (StructuralListLengthBasic.code_member _ _ _ hn)
  have hCase := at_fields w n h S r l L hp
  exact .impE (.impE (.impE (.impE (.impE hCase hh) hn) hS) hSp) hL

end PPAC.Migration.Internal.StructuralListSpliceSnoc
