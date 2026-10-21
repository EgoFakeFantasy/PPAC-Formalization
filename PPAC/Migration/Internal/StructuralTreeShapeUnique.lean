import PPAC.Migration.Internal.StructuralTreeEncodeSyntax

/-! 结构Shape四分量唯一不预设子树有效；供任意候选构造与真正解码对齐。 -/
namespace PPAC.Migration.Internal.StructuralTreeShapeUnique
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralTreeOperatorSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem payload_subst {m} {Γ : Context m} (w n tag p q l f : Fin m) (he : Derives Γ (.equal p q))
    (hd : Derives Γ (shape w n tag p l f)) : Derives Γ (shape w n tag q l f) := by
  have hi : Derives Γ ((shape w.castSucc n.castSucc tag.castSucc (Fin.last m) l.castSucc f.castSucc).instantiate p) := by
    simpa only [Formula.instantiate, shape_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd
  have ho := Derives.eqSubst (shape w.castSucc n.castSucc tag.castSucc (Fin.last m) l.castSucc f.castSucc) he hi
  simpa only [Formula.instantiate, shape_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n tag p l f other q k g : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n tag p l f)) (ht : Derives Γ (shape w n other q k g)) :
    Derives Γ (((Formula.equal tag other).conj (.equal p q)).conj ((Formula.equal l k).conj (.equal f g))) := by
  have hp := StructuralListLengthBasic.code_member _ _ _ (.conjL (.conjR hs))
  have hq := StructuralListLengthBasic.code_member _ _ _ (.conjL (.conjR ht))
  have he := StructuralNodeCore.injective hZ _ _ _ _ _ _ hw (.conjL (.conjL hs)) hp (.conjL (.conjL ht)) hq
    (.conjR (.conjL hs)) (.conjR (.conjL ht))
  have hSame := payload_subst _ _ _ _ _ _ _ (eq_symm (.conjR he)) ht
  exact .conjI he (StructuralListFieldDecode.unique_pair hZ _ _ _ _ _ _ hw (.conjL (.conjR hs)) (.conjL (.conjR hSame))
    (.conjR (.conjR hs)) (.conjR (.conjR hSame)))
end PPAC.Migration.Internal.StructuralTreeShapeUnique
