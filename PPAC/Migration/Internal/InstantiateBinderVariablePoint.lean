import PPAC.Migration.Internal.InstantiateBinderGeometry
import PPAC.Migration.Internal.InstantiateVariableSpecialization
import PPAC.Migration.Internal.InstantiateClosedParameterRename
import PPAC.Migration.Internal.SyntaxIndexLiftOrder

/-! 原mode2合法bound的below／point两分支在实际binder重命名下协变。 -/
namespace PPAC.Migration.Internal.InstantiateBinderVariablePoint
open Source SourceAlgebra SourceLogic OmegaSyntax InstantiateVariableValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem rename_input_iff {m} {Γ : Context m} (w U V c e C t P q : Fin m)
    (he : Derives Γ (.equal t P)) :
    Derives Γ ((SyntaxRenameTermSyntax.renamed w U V c e C e t q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e P q)) := by
  let F := SyntaxRenameTermSyntax.renamed w.castSucc U.castSucc V.castSucc c.castSucc e.castSucc C.castSucc e.castSucc (Fin.last m) q.castSucc
  apply Derives.conjI
  · apply Derives.impI
    let E := SyntaxRenameTermSyntax.renamed w U V c e C e t q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hi : Derives (Context.add E Γ) (F.instantiate t) := of_eq (by simp only [F, E, Formula.instantiate, SyntaxRenameTermSyntax.renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hE
    exact of_eq (by simp only [F, Formula.instantiate, SyntaxRenameTermSyntax.renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.eqSubst F (add he _) hi)
  · apply Derives.impI
    let E := SyntaxRenameTermSyntax.renamed w U V c e C e P q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hi : Derives (Context.add E Γ) (F.instantiate P) := of_eq (by simp only [F, E, Formula.instantiate, SyntaxRenameTermSyntax.renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hE
    exact of_eq (by simp only [F, Formula.instantiate, SyntaxRenameTermSyntax.renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.eqSubst F (add (eq_symm he) _) hi)

theorem preserved {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d P i D I U V c e C X t q : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w))
    (hD : Derives Γ (successor D d)) (hI : Derives Γ (successor I i)) (hBelow : Derives Γ (.mem i d))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (ht : Derives Γ (SyntaxTermSyntax.term w c e t)) (hv : Derives Γ (SyntaxVariableSyntax.code true w i t))
    (hX : Derives Γ (SyntaxVariableSyntax.code true w I X)) :
    Derives Γ ((boundValue w D P I X q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q)) := by
  have hi := SyntaxVariableDecode.index_natural true w i t hv
  have hDn := OmegaStructureAlgebra.successor_member w D d (ZFContext.arithmetic hZ).base.extensionality hw hd hD
  have hID := SyntaxIndexLiftOrder.successor_member hZ w i d I D hw hi hd hBelow hI hD
  have hn := InstantiateVariableSpecialization.below_iff hZ w D P I X q hw hDn hID
  have hc := AbstractBinderRename.code_iff_equal hZ true w I X q hw hX
  have hr := AbstractBinderRename.bound_at hZ w U V c e C t q i I hw hU hV ht hv hI
  exact SyntaxTypeLocalTransfer.iff_trans hn (SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hc) (.conjL hc)) (.conjI (.conjR hr) (.conjL hr)))

theorem at_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d P i D I U V c e C X t q : Fin m)
    (hw : Derives Γ (omega w)) (hD : Derives Γ (successor D d)) (hI : Derives Γ (successor I i))
    (he : Derives Γ (.equal i d))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (hp : Derives Γ (InstantiateOperationFrameSyntax.closedParameter w e P)) (ht : Derives Γ (.equal t P)) :
    Derives Γ ((boundValue w D P I X q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q)) := by
  have hiD := InstantiateBinderGeometry.successor_point hZ d i D I he hD hI
  have hn := InstantiateVariableSpecialization.at_point_iff hZ w D P I X q hiD
  have hr := SyntaxTypeLocalTransfer.iff_trans (rename_input_iff w U V c e C t P q ht)
    (InstantiateClosedParameterRename.closed_iff hZ w U V c e C P q hw hU hV hp)
  exact SyntaxTypeLocalTransfer.iff_trans hn (.conjI (.conjR hr) (.conjL hr))

end PPAC.Migration.Internal.InstantiateBinderVariablePoint
