import PPAC.Migration.Internal.SyntaxRenameTermAtIndex
import PPAC.Migration.Internal.SyntaxFreeShiftGraph
import PPAC.Migration.Internal.SyntaxIdentityUnique

/-! 原binder使用的实际bound后继图／free恒等图，对所有变量输出的精确重命名律。 -/
namespace PPAC.Migration.Internal.AbstractBinderRename
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem code_iff_equal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w i n q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxVariableSyntax.code bound w i n)) :
    Derives Γ ((SyntaxVariableSyntax.code bound w i q).iff (.equal q n)) := by
  apply Derives.conjI
  · exact .impI (SyntaxVariables.unique (ZFContext.add hZ _) bound w i q n (add hw _) (.hyp (Or.inl rfl)) (add hn _))
  · apply Derives.impI
    let E := Formula.equal q n
    let F := SyntaxVariableSyntax.code bound w.castSucc i.castSucc (Fin.last m)
    have hs : Derives (Context.add E Γ) (F.instantiate n) := of_eq (by simp only [F, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (add hn E)
    have ho := Derives.eqSubst F (eq_symm (.hyp (Or.inl rfl))) hs
    exact of_eq (by simp only [F, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ho

theorem bound_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w U V c e C t q i j : Fin m)
    (hw : Derives Γ (omega w)) (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U))
    (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (ht : Derives Γ (SyntaxTermSyntax.term w c e t))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w i t)) (hj : Derives Γ (successor j i)) :
    Derives Γ ((SyntaxRenameTermSyntax.renamed w U V c e C e t q).iff (SyntaxVariableSyntax.code true w j q)) := by
  have hi := SyntaxTerms.member hZ true w c e t i hw hv ht
  have he := Derives.impE (.conjR (SyntaxFreeShiftGraph.edge_iff c U i j (SyntaxFreeShiftGraph.to_graph w c C U hU))) (.conjI hi hj)
  exact SyntaxRenameTermAtIndex.renamed_at hZ true w U V c e C e t q i j hw (.conjI (.conjL (.conjR hU)) (.conjL hV)) hi he hv

theorem free_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w U V c e C t q i : Fin m)
    (hw : Derives Γ (omega w)) (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U))
    (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (ht : Derives Γ (SyntaxTermSyntax.term w c e t))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w i t)) :
    Derives Γ ((SyntaxRenameTermSyntax.renamed w U V c e C e t q).iff (SyntaxVariableSyntax.code false w i q)) := by
  have hi := SyntaxTerms.member hZ false w c e t i hw hv ht
  have he := SyntaxIdentityUnique.diagonal_edge w e V i (.conjL hV) (.conjR hV) hi
  exact SyntaxRenameTermAtIndex.renamed_at hZ false w U V c e C e t q i i hw (.conjI (.conjL (.conjR hU)) (.conjL hV)) hi he hv

end PPAC.Migration.Internal.AbstractBinderRename
