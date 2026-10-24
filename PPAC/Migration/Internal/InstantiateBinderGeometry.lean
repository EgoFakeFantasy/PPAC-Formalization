import PPAC.Migration.Internal.InstantiateOperationFrameSyntax
import PPAC.Migration.Internal.SyntaxCodedMixedBinderTyping

/-! 原mode2深度与独立源／目标后继的实际对象几何；不预先识别两后继。 -/
namespace PPAC.Migration.Internal.InstantiateBinderGeometry
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem successor_base_subst {m} {Γ : Context m} (A a d : Fin m)
    (he : Derives Γ (.equal a d)) (hs : Derives Γ (successor A a)) : Derives Γ (successor A d) := by
  let F := successor A.castSucc (Fin.last m)
  have hi : Derives Γ (F.instantiate a) := of_eq (by simp only [F, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hs
  exact of_eq (by simp only [F, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.eqSubst F he hi)

theorem successor_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (d i D I : Fin m)
    (he : Derives Γ (.equal i d)) (hD : Derives Γ (successor D d)) (hI : Derives Γ (successor I i)) :
    Derives Γ (.equal I D) :=
  OmegaUniversal.successor_unique I D d (ZFContext.arithmetic hZ).base.extensionality
    (successor_base_subst I i d he hI) hD

theorem lifted_contexts {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (d a b c e D A C : Fin m)
    (hc : Derives Γ (InstantiateOperationFrameSyntax.contextsAtDepth d a b c e))
    (hD : Derives Γ (successor D d)) (hA : Derives Γ (successor A a)) (hC : Derives Γ (successor C c)) :
    Derives Γ (InstantiateOperationFrameSyntax.contextsAtDepth D A b C e) := by
  have haD := OmegaUniversal.successor_unique a D d (ZFContext.arithmetic hZ).base.extensionality (.conjL hc) hD
  have hCD := successor_point hZ d c D C (.conjL (.conjR hc)) hD hC
  exact .conjI (successor_base_subst A a D haD hA) (.conjI hCD (.conjR (.conjR hc)))

end PPAC.Migration.Internal.InstantiateBinderGeometry
