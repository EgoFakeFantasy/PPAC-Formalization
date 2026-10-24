import PPAC.Migration.Internal.AbstractBoundOrder
import PPAC.Migration.Internal.AbstractBinderRename

/-! 任意内部深度下原mode1变量数值关系与实际binder图重命名的四分支协变。 -/
namespace PPAC.Migration.Internal.AbstractBinderVariablePoint
open Source SourceAlgebra SourceLogic OmegaSyntax AbstractVariableValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem preserved {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d i D I U V c e C X t q : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w))
    (hD : Derives Γ (successor D d)) (hI : Derives Γ (successor I i)) (hBelow : Derives Γ (.mem i d))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (ht : Derives Γ (SyntaxTermSyntax.term w c e t)) (hv : Derives Γ (SyntaxVariableSyntax.code true w i t))
    (hX : Derives Γ (SyntaxVariableSyntax.code true w I X)) :
    Derives Γ ((boundValue w D I X q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q)) := by
  have hi := SyntaxVariableDecode.index_natural true w i t hv
  have hDn := OmegaStructureAlgebra.successor_member w D d (ZFContext.arithmetic hZ).base.extensionality hw hd hD
  have hID := SyntaxIndexLiftOrder.successor_member hZ w i d I D hw hi hd hBelow hI hD
  have hn := AbstractVariableSpecialization.bound_below_iff hZ w D I X q hw hDn hID
  have hc := AbstractBinderRename.code_iff_equal hZ true w I X q hw hX
  have hr := AbstractBinderRename.bound_at hZ w U V c e C t q i I hw hU hV ht hv hI
  exact SyntaxTypeLocalTransfer.iff_trans hn (SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hc) (.conjL hc)) (.conjI (.conjR hr) (.conjL hr)))

theorem shifted_at_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d i D I J U V c e C X t q : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (hi : Derives Γ (.mem i w))
    (hD : Derives Γ (successor D d)) (hI : Derives Γ (successor I i)) (hJ : Derives Γ (successor J I))
    (hAbove : Derives Γ (.mem d I))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (ht : Derives Γ (SyntaxTermSyntax.term w c e t)) (hv : Derives Γ (SyntaxVariableSyntax.code true w I t)) :
    Derives Γ ((boundValue w D I X q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q)) := by
  have hn := AbstractBoundOrder.above_successor_iff hZ w d i D I J X q hw hd hi hD hI hJ hAbove
  have hr := AbstractBinderRename.bound_at hZ w U V c e C t q I J hw hU hV ht hv hJ
  exact SyntaxTypeLocalTransfer.iff_trans hn (.conjI (.conjR hr) (.conjL hr))

theorem shifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d i D I U V c e C X t q : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (hi : Derives Γ (.mem i w))
    (hD : Derives Γ (successor D d)) (hI : Derives Γ (successor I i)) (hAbove : Derives Γ (.mem d I))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (ht : Derives Γ (SyntaxTermSyntax.term w c e t)) (hv : Derives Γ (SyntaxVariableSyntax.code true w I t)) :
    Derives Γ ((boundValue w D I X q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q)) := by
  let E := successor (Fin.last m) I.castSucc
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (InsertExistence.exists_insert I I (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hd1 : Derives Δ (.mem d.castSucc w.castSucc) := under hd E
  have hi1 : Derives Δ (.mem i.castSucc w.castSucc) := under hi E
  have hD1 := of_eq (successor_rename D d Fin.castSucc) (under hD E)
  have hI1 := of_eq (successor_rename I i Fin.castSucc) (under hI E)
  have ha1 : Derives Δ (.mem d.castSucc I.castSucc) := under hAbove E
  have hU1 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w c C U Fin.castSucc) (under hU E)
  have hV1 := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w e V Fin.castSucc) (under hV E)
  have ht1 := of_eq (SyntaxTermSyntax.term_rename w c e t Fin.castSucc) (under ht E)
  have hv1 := of_eq (SyntaxVariableSyntax.code_rename true w I t Fin.castSucc) (under hv E)
  have ho := shifted_at_successor (ZFContext.under hZ E) w.castSucc d.castSucc i.castSucc D.castSucc I.castSucc (Fin.last m) U.castSucc V.castSucc c.castSucc e.castSucc C.castSucc X.castSucc t.castSucc q.castSucc hw1 hd1 hi1 hD1 hI1 (.hyp (Or.inl rfl)) ha1 hU1 hV1 ht1 hv1
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, boundValue_rename, SyntaxRenameTermSyntax.renamed_rename]) ho

theorem free_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d i D U V c e C t q : Fin m)
    (hw : Derives Γ (omega w)) (hD : Derives Γ (successor D d)) (hz : Derives Γ (empty i))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (ht : Derives Γ (SyntaxTermSyntax.term w c e t)) (hv : Derives Γ (SyntaxVariableSyntax.code true w d t)) :
    Derives Γ ((freeValue w D i q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q)) := by
  have hn := AbstractVariableSpecialization.free_zero_iff w D i q hz
  have hr := AbstractBinderRename.bound_at hZ w U V c e C t q d D hw hU hV ht hv hD
  exact SyntaxTypeLocalTransfer.iff_trans hn (.conjI (.conjR hr) (.conjL hr))

theorem free_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i j D U V c e C t q : Fin m)
    (hw : Derives Γ (omega w)) (hij : Derives Γ (successor i j))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (ht : Derives Γ (SyntaxTermSyntax.term w c e t)) (hv : Derives Γ (SyntaxVariableSyntax.code false w j t)) :
    Derives Γ ((freeValue w D i q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q)) := by
  have hj := SyntaxVariableDecode.index_natural false w j t hv
  have hn := AbstractVariableSpecialization.free_successor_iff hZ w D i j q hw hj hij
  have hr := AbstractBinderRename.free_at hZ w U V c e C t q j hw hU hV ht hv
  exact SyntaxTypeLocalTransfer.iff_trans hn (.conjI (.conjR hr) (.conjL hr))

end PPAC.Migration.Internal.AbstractBinderVariablePoint
