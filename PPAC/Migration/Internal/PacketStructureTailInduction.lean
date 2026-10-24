import PPAC.Migration.Internal.PacketStructureTailPoint

/-! Original Foundation with the fixed joint matrix's full Separation instance discharges every internal child IH. -/
namespace PPAC.Migration.Internal.PacketStructureTailInduction
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketStructureAcceptedSyntax PacketStructureTailSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem tree_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (hypothesis w n)) : Derives Γ (treeProperty w n) := by
  apply OriginalUniversalBlock.intro_many 2
  apply Derives.impI
  let H := tree (old 2 w : Fin (m+2)) (old 2 n) (slot 2 0) (slot 2 1)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw H)
  have hi2 := of_eq (hypothesis_rename w n (old 2)) (HornBinderRules.under_body 2 hi H)
  exact PacketStructureTailPoint.tree_point (HornBinderRules.zf_body 2 hZ H) (old 2 w) (old 2 n) (slot 2 0) (slot 2 1) hw2 hi2 (.hyp (Or.inl rfl))

theorem forest_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (hypothesis w n)) : Derives Γ (forestProperty w n) := by
  apply OriginalUniversalBlock.intro_many 3
  apply Derives.impI
  let H := forest (old 3 w : Fin (m+3)) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2)
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw H)
  have hi3 := of_eq (hypothesis_rename w n (old 3)) (HornBinderRules.under_body 3 hi H)
  exact PacketStructureTailPoint.forest_point (HornBinderRules.zf_body 3 hZ H) (old 3 w) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hi3 (.hyp (Or.inl rfl))

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (hypothesis w n)) : Derives Γ (property w n) :=
  .conjI (tree_property hZ w n hw hi) (forest_property hZ w n hw hi)

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (BoundedInduction.progressive PacketStructureTailSyntax.matrix (fun _ : Fin 1 => w) w) := by
  simp only [BoundedInduction.progressive,PacketStructureTailSyntax.matrix_pred,ReplacementPredicates.paramsUp]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let N := Formula.mem (Fin.last m) w.castSucc
  let I := hypothesis w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add N (Context.image Formula.raise Γ))
  have hZ1 := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) N) I
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  exact point hZ1 w.castSucc (Fin.last m) (add (add hw1 N) I) hI

theorem all_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))) := by
  have hi := BoundedInduction.induction_on_set PacketStructureTailSyntax.matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ PacketStructureTailSyntax.matrix.neg) (ZFContext.arithmetic hZ).base.foundation (progressive hZ w hw)
  simpa only [BoundedInduction.holds,PacketStructureTailSyntax.matrix_pred,ReplacementPredicates.paramsUp] using hi

end PPAC.Migration.Internal.PacketStructureTailInduction
