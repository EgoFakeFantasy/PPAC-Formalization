import PPAC.Migration.Internal.InstantiateBinderVariablePoint

/-! 源长度succ(depth)下全部合法内部变量的原mode2 binder协变，无超阈值分支假设。 -/
namespace PPAC.Migration.Internal.InstantiateBinderVariable
open Source SourceAlgebra SourceLogic OmegaSyntax InstantiateVariableValueSyntax

theorem bound_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d P a i D I U V c e C x X t q : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w))
    (ha : Derives Γ (successor a d)) (hi : Derives Γ (.mem i a))
    (hD : Derives Γ (successor D d)) (hI : Derives Γ (successor I i))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (ht : Derives Γ (SyntaxTermSyntax.term w c e t))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w i x)) (hX : Derives Γ (SyntaxVariableSyntax.code true w I X))
    (hp : Derives Γ (InstantiateOperationFrameSyntax.closedParameter w e P)) (hv : Derives Γ (boundValue w d P i x t)) :
    Derives Γ ((boundValue w D P I X q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q)) := by
  apply Derives.disjE (InsertLogic.member_cases a d d i ha hi)
  · let E := Formula.mem i d
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have htx := Derives.impE (.conjL (InstantiateVariableSpecialization.below_iff (ZFContext.add hZ E) w d P i x t (add hw E) (add hd E) hE)) (add hv E)
    have hc := Derives.impE (.conjR (AbstractBinderRename.code_iff_equal (ZFContext.add hZ E) true w i x t (add hw E) (add hx E))) htx
    exact InstantiateBinderVariablePoint.preserved (ZFContext.add hZ E) w d P i D I U V c e C X t q
      (add hw E) (add hd E) (add hD E) (add hI E) hE (add hU E) (add hV E) (add ht E) hc (add hX E)
  · let E := Formula.equal i d
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have htp := Derives.impE (.conjL (InstantiateVariableSpecialization.at_point_iff (ZFContext.add hZ E) w d P i x t hE)) (add hv E)
    exact InstantiateBinderVariablePoint.at_point (ZFContext.add hZ E) w d P i D I U V c e C X t q
      (add hw E) (add hD E) (add hI E) hE (add hU E) (add hV E) (add hp E) htp

theorem free_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i U V c e C X t q : Fin m)
    (hw : Derives Γ (omega w))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (ht : Derives Γ (SyntaxTermSyntax.term w c e t)) (hx : Derives Γ (SyntaxVariableSyntax.code false w i X))
    (hv : Derives Γ (.equal t X)) :
    Derives Γ ((Formula.equal q X).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q)) := by
  have hc := Derives.impE (.conjR (AbstractBinderRename.code_iff_equal hZ false w i X t hw hx)) hv
  have hr := AbstractBinderRename.free_at hZ w U V c e C t q i hw hU hV ht hc
  have he := AbstractBinderRename.code_iff_equal hZ false w i X q hw hx
  have ho := SyntaxTypeLocalTransfer.iff_trans hr he
  exact .conjI (.conjR ho) (.conjL ho)

end PPAC.Migration.Internal.InstantiateBinderVariable
