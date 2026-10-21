import PPAC.Migration.Internal.StructuralTreeEncode

/-! 原树构造后的精确字段回读、全部子树有效性反射及解码后原码恢复。 -/
namespace PPAC.Migration.Internal.StructuralTreeEncodeReadback
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralTreeOperatorSyntax StructuralTreeEncodeSyntax StructuralTreeValiditySyntax
open StructuralListLengthSyntax (under_four zf_under_four)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem children_subst {m} {Γ : Context m} (w f g : Fin m) (he : Derives Γ (.equal f g))
    (hv : Derives Γ (validChildren w f)) : Derives Γ (validChildren w g) := by
  have hi : Derives Γ ((validChildren w.castSucc (Fin.last m)).instantiate f) := by
    simpa only [Formula.instantiate, validChildren_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hv
  have ho := Derives.eqSubst (validChildren w.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, validChildren_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem children_of_shape {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n tag p l f : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n tag p l f)) (hv : Derives Γ (valid w n)) : Derives Γ (validChildren w f) := by
  have hr := StructuralTreeRecursion.valid_to_recursive hZ w n hw hv
  let D := dataBody w n
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_recursive w n _ hr
  have hZ4 : ZFContext.Evidence Δ := zf_under_four hZ D
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_four hw D
  have hs4 : Derives Δ (shape w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
      tag.castSucc.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, shape_rename] using under_four hs D
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have heq := StructuralTreeShapeUnique.unique hZ4 _ _ _ _ _ _ _ _ _ _ hw4 (.conjL hD) hs4
  have hout := children_subst _ _ _ (.conjR (.conjR heq)) (.conjR hD)
  simpa only [Formula.raise, validChildren_rename] using hout

theorem encoding_valid {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag l f n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (encoding w tag l f n)) (hv : Derives Γ (validChildren w f)) : Derives Γ (valid w n) := by
  let E := encodingBody w tag l f n
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply eliminate_encoding w tag l f n _ he
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  have hv1 : Derives Δ (validChildren w.castSucc f.castSucc) := by simpa only [Formula.raise, validChildren_rename] using under hv E
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hr := intro_recursive _ _ _ _ _ _ (.conjI hE hv1)
  have hout := StructuralTreeDecode.recursive_to_valid (ZFContext.under hZ E) _ _ hw1 hr
  simpa only [Formula.raise, valid_rename] using hout

theorem valid_children {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag l f n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (encoding w tag l f n)) (hv : Derives Γ (valid w n)) : Derives Γ (validChildren w f) := by
  let E := encodingBody w tag l f n
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply eliminate_encoding w tag l f n _ he
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  have hv1 : Derives Δ (valid w.castSucc n.castSucc) := by simpa only [Formula.raise, valid_rename] using under hv E
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hout := children_of_shape (ZFContext.under hZ E) _ _ _ _ _ _ hw1 hE hv1
  simpa only [Formula.raise, validChildren_rename] using hout

theorem valid_iff_children {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag l f n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (encoding w tag l f n)) : Derives Γ ((valid w n).iff (validChildren w f)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact valid_children (ZFContext.add hZ _) _ _ _ _ _ (add hw _) (add he _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact encoding_valid (ZFContext.add hZ _) _ _ _ _ _ (add hw _) (add he _) (.hyp (Or.inl rfl))

theorem decode_after_encode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag l f n other p k g : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (encoding w tag l f n)) (hs : Derives Γ (shape w n other p k g)) :
    Derives Γ (((Formula.equal other tag).conj (.equal k l)).conj (.equal g f)) := by
  let E := encodingBody w tag l f n
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply eliminate_encoding w tag l f n _ he
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  have hs1 : Derives Δ (shape w.castSucc n.castSucc other.castSucc p.castSucc k.castSucc g.castSucc) := by simpa only [Formula.raise, shape_rename] using under hs E
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have heq := StructuralTreeShapeUnique.unique (ZFContext.under hZ E) _ _ _ _ _ _ _ _ _ _ hw1 hs1 hE
  exact .conjI (.conjI (.conjL (.conjL heq)) (.conjL (.conjR heq))) (.conjR (.conjR heq))

theorem decode_then_encode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n tag p l f r : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n tag p l f)) (he : Derives Γ (encoding w tag l f r)) : Derives Γ (.equal r n) :=
  StructuralTreeEncode.unique hZ _ _ _ _ _ _ hw he (intro_encoding _ _ _ _ _ _ hs)
end PPAC.Migration.Internal.StructuralTreeEncodeReadback
