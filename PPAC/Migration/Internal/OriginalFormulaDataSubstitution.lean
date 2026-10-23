import PPAC.Migration.Internal.OriginalFormulaCaseSyntax

/-! 原公式局部数据的元数据等词传输；量词子深度可保持为同一实际对象。 -/
namespace PPAC.Migration.Internal.OriginalFormulaDataSubstitution
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem binary_metadata {m} {Γ : Context m} (tag kind : Nat) (w mode depth parameter n q x y X Y M D P : Fin m)
    (hm : Derives Γ (.equal mode M)) (hd : Derives Γ (.equal depth D)) (hp : Derives Γ (.equal parameter P))
    (hv : Derives Γ (OriginalFormulaLocalData.binary tag kind w mode depth parameter n q x y X Y)) :
    Derives Γ (OriginalFormulaLocalData.binary tag kind w M D P n q x y X Y) :=
  .conjI (.conjL hv) (.conjI (OriginalRowMetadataSubstitution.run_fields kind w mode depth parameter x X M D P hm hd hp (.conjL (.conjR hv)))
    (OriginalRowMetadataSubstitution.run_fields kind w mode depth parameter y Y M D P hm hd hp (.conjR (.conjR hv))))

theorem unary_metadata {m} {Γ : Context m} (tag : Nat) (w mode depth parameter n q x X M D P : Fin m)
    (hm : Derives Γ (.equal mode M)) (hd : Derives Γ (.equal depth D)) (hp : Derives Γ (.equal parameter P))
    (hv : Derives Γ (OriginalFormulaLocalData.unary tag w mode depth parameter n q x X)) :
    Derives Γ (OriginalFormulaLocalData.unary tag w M D P n q x X) :=
  .conjI (.conjL hv) (OriginalRowMetadataSubstitution.run_fields 3 w mode depth parameter x X M D P hm hd hp (.conjR hv))

theorem application_metadata {m} {Γ : Context m}  (w mode depth parameter n q symbol args newArgs M D P : Fin m)
    (hm : Derives Γ (.equal mode M)) (hd : Derives Γ (.equal depth D)) (hp : Derives Γ (.equal parameter P))
    (hv : Derives Γ (OriginalFormulaLocalData.application w mode depth parameter n q symbol args newArgs)) :
    Derives Γ (OriginalFormulaLocalData.application w M D P n q symbol args newArgs) :=
  .conjI (.conjL hv) (OriginalRowMetadataSubstitution.run_fields 2 w mode depth parameter args newArgs M D P hm hd hp (.conjR hv))

theorem unary_case_depth {m} {Γ : Context m} (tag : Nat) (w mode depth parameter n q D : Fin m)
    (he : Derives Γ (.equal depth D)) (hu : Derives Γ (OriginalFormulaCaseSyntax.unaryCase tag w mode depth parameter n q)) :
    Derives Γ (OriginalFormulaCaseSyntax.unaryCase tag w mode D parameter n q) := by
  let P := OriginalFormulaCaseSyntax.unaryCase tag w.castSucc mode.castSucc (Fin.last m) parameter.castSucc n.castSucc q.castSucc
  have h0 : P.instantiate depth = OriginalFormulaCaseSyntax.unaryCase tag w mode depth parameter n q := by simp only [P, Formula.instantiate, OriginalFormulaCaseSyntax.unaryCase_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate D = OriginalFormulaCaseSyntax.unaryCase tag w mode D parameter n q := by simp only [P, Formula.instantiate, OriginalFormulaCaseSyntax.unaryCase_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hu))

end PPAC.Migration.Internal.OriginalFormulaDataSubstitution
