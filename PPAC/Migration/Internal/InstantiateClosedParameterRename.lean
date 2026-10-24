import PPAC.Migration.Internal.InstantiateOperationFrameSyntax
import PPAC.Migration.Internal.AbstractBinderRename

/-! mode2 的空绑定参数在实际 binder 的 bound 后移／free 恒等图下保持原码。 -/
namespace PPAC.Migration.Internal.InstantiateClosedParameterRename
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem from_free_branch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w U V c e C P q : Fin m)
    (hw : Derives Γ (omega w)) (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U))
    (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (hp : Derives Γ (SyntaxTermSyntax.branch false w e P)) :
    Derives Γ ((SyntaxRenameTermSyntax.renamed w U V c e C e P q).iff (.equal q P)) := by
  let B := SyntaxTermSyntax.branchWitness false w e P
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxTermSyntax.eliminate_branch false w e P _ hp
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hU1 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w c C U Fin.castSucc) (under hU B)
  have hV1 := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w e V Fin.castSucc) (under hV B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hcontexts : Derives Δ (SyntaxTermSyntax.contexts w.castSucc c.castSucc e.castSucc) :=
    .conjI (.conjL (.conjL (.conjL (.conjR hU1)))) (.conjL (.conjL (.conjL hV1)))
  have ht := SyntaxTermSyntax.intro_term false w.castSucc c.castSucc e.castSucc P.castSucc (Fin.last m)
    (.conjI hcontexts (.conjL hB)) (.conjR hB)
  have hr := AbstractBinderRename.free_at hZ1 w.castSucc U.castSucc V.castSucc c.castSucc e.castSucc C.castSucc P.castSucc q.castSucc (Fin.last m)
    hw1 hU1 hV1 ht (.conjR hB)
  have he := AbstractBinderRename.code_iff_equal hZ1 false w.castSucc (Fin.last m) P.castSucc q.castSucc hw1 (.conjR hB)
  have ho := SyntaxTypeLocalTransfer.iff_trans hr he
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, SyntaxRenameTermSyntax.renamed_rename]) ho

theorem closed_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w U V c e C P q : Fin m)
    (hw : Derives Γ (omega w)) (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U))
    (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (hp : Derives Γ (InstantiateOperationFrameSyntax.closedParameter w e P)) :
    Derives Γ ((SyntaxRenameTermSyntax.renamed w U V c e C e P q).iff (.equal q P)) :=
  from_free_branch hZ w U V c e C P q hw hU hV
    (InstantiateOperationFrameSyntax.closedParameter_free w e P hp)

end PPAC.Migration.Internal.InstantiateClosedParameterRename
