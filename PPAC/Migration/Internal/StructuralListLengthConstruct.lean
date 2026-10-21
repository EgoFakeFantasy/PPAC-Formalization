import PPAC.Migration.Internal.ObjectStructuralListFields

/-! 原Nil/Cons在指定实际长度上的构造；长度替换只用原对象等词规则。 -/
namespace PPAC.Migration.Internal.StructuralListLengthConstruct
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListLengthSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem length_subst {m} {Γ : Context m} (w n l k : Fin m) (he : Derives Γ (.equal l k))
    (hl : Derives Γ (hasLength w n l)) : Derives Γ (hasLength w n k) := by
  have hi : Derives Γ ((hasLength w.castSucc n.castSucc (Fin.last m)).instantiate l) := by
    simpa only [Formula.instantiate, hasLength_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hl
  have ho := Derives.eqSubst (hasLength w.castSucc n.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, hasLength_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem nil_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n z : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) (hz : Derives Γ (empty z)) : Derives Γ (hasLength w n z) := by
  have hv := StructuralListTraceBase.valid_nil hZ w n hw hn
  have hl := StructuralListLengthBasic.exists_length w n hv
  let L := (Formula.mem (Fin.last m) w.castSucc).conj (hasLength w.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add L (Context.image Formula.raise Γ)
  change Derives Γ (.ex L) at hl
  apply Derives.exE (p := L) hl
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ L
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw L
  have hn1 : Derives Δ (nilCode w.castSucc n.castSucc) := by simpa only [Formula.raise, nilCode_rename] using under hn L
  have hz1 : Derives Δ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz L
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have he := StructuralListLengthRules.nil_empty hZ1 _ _ _ hw1 hn1 (.conjR hL)
  have heq := OmegaUniversal.empty_unique _ _ (ZFContext.arithmetic hZ1).base.extensionality he hz1
  have hout := length_subst _ _ _ _ heq (.conjR hL)
  simpa only [Formula.raise, hasLength_rename] using hout

theorem cons_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n r s : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hc : Derives Γ (consCode w h t n))
    (hr : Derives Γ (hasLength w t r)) (hs : Derives Γ (successor s r)) : Derives Γ (hasLength w n s) := by
  have hv := StructuralListValidity.cons_valid hZ w h t n hw hh (StructuralListLengthBasic.valid_of_length w t r hr) hc
  have hl := StructuralListLengthBasic.exists_length w n hv
  let L := (Formula.mem (Fin.last m) w.castSucc).conj (hasLength w.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add L (Context.image Formula.raise Γ)
  change Derives Γ (.ex L) at hl
  apply Derives.exE (p := L) hl
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ L
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw L
  have hc1 : Derives Ξ (consCode w.castSucc h.castSucc t.castSucc n.castSucc) := by simpa only [Formula.raise, consCode_rename] using under hc L
  have hr1 : Derives Ξ (hasLength w.castSucc t.castSucc r.castSucc) := by simpa only [Formula.raise, hasLength_rename] using under hr L
  have hL : Derives Ξ L := .hyp (Or.inl rfl)
  have ht1 := StructuralListLengthBasic.code_member _ _ _ hr1
  have hp := StructuralListLengthRules.cons_predecessor hZ1 _ _ _ _ _ hw1 (under hh L) ht1 hc1 (.conjR hL)
  let P := ((Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last m).castSucc (Fin.last (m+1)))).conj
    (hasLength w.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add P (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 P
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 P
  have hr2 : Derives Δ (hasLength w.castSucc.castSucc t.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise, hasLength_rename] using under hr1 P
  have hs2 : Derives Δ (successor s.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using under (under hs L) P
  have hL2 : Derives Δ (hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := by simpa only [Formula.raise, hasLength_rename] using under (.conjR hL) P
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have heq := StructuralListLengthUnique.unique hZ2 _ _ _ _ hw2 (.conjR hP) hr2
  have hsucc := GodelUnpairArithmetic.successor_base_subst _ _ _ heq (.conjR (.conjL hP))
  have hout := length_subst _ _ _ _ (OmegaUniversal.successor_unique _ _ _ (ZFContext.arithmetic hZ2).base.extensionality hsucc hs2) hL2
  simpa only [Formula.raise, hasLength_rename] using hout

theorem nil_of_empty_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n z : Fin m)
    (hl : Derives Γ (hasLength w n z)) (hz : Derives Γ (empty z)) : Derives Γ (nilCode w n) := by
  let L := lengthBody w n z
  let Δ := Context.add L (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_length w n z _ hl
  have hZ4 : ZFContext.Evidence Δ := zf_under_four hZ L
  have hz4 : Derives Δ (empty z.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using under_four hz L
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hout := StructuralListTraceInvert.zero_case hZ4 _ _ _ _ _ _ _ hL hz4
  simpa only [Formula.raise, nilCode_rename] using hout
end PPAC.Migration.Internal.StructuralListLengthConstruct
