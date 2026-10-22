import PPAC.Migration.Internal.SyntaxTermImagePrefixPoint

/-! 新头槽与后继源索引的全内部单值性；实际旧表单值和后继单射均在原对象核中。 -/
namespace PPAC.Migration.Internal.SyntaxTermImagePrefixUnique
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxTermImagePrefixSyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c d z i q v : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (imageMap w f a c d))
    (hq : Derives Γ (value f a z i q)) (hv : Derives Γ (value f a z i v)) : Derives Γ (.equal q v) := by
  apply Derives.disjE hq
  · let Z := (empty i).conj (Formula.equal q z)
    have hZp : Derives (Context.add Z Γ) Z := .hyp (Or.inl rfl)
    have he := SyntaxTermImagePrefixPoint.zero_iff f a z i v (.conjL hZp)
    exact eq_trans (.conjR hZp) (eq_symm (.impE (.conjL he) (add hv Z)))
  · let V := shifted f a i q
    let B := shiftedBody f a i q
    let Δ := Context.add B (Context.image Formula.raise (Context.add V Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ V) B
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw V) B)
    have hf1 : Derives Δ (imageMap w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc) := of_eq (imageMap_rename w f a c d Fin.castSucc) (under (add hf V) B)
    have hv1 : Derives Δ (value f.castSucc a.castSucc z.castSucc i.castSucc v.castSucc) := of_eq (value_rename f a z i v Fin.castSucc) (under (add hv V) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hk := StructuralListTraceOrder.member_member hZ1 _ _ _ hw1 (.conjL hf1) (.conjL hB)
    have hd := SyntaxTermImagePrefixPoint.successor_forward hZ1 _ _ _ _ _ _ _ hw1 hk (.conjL (.conjR hB)) hv1
    exact GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ1).base.extensionality
      (SyntaxTermImageSyntax.image_function _ _ _ _ _ hf1) (.conjR (.conjR hB)) (.conjR hd)

end PPAC.Migration.Internal.SyntaxTermImagePrefixUnique
