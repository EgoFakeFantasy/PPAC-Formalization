import PPAC.Migration.Internal.StructuralListFieldGraphFiber

/-! 有效内部列表实际解码为唯一长度和完整有序字段图；尚不宣称任意字段序列的逆编码往返。 -/
namespace PPAC.Migration.Internal.StructuralListFieldDecode
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListLengthSyntax StructuralListFieldPairSyntax StructuralListFieldGraphSyntax
open StructuralListTraceSyntax (valid valid_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem eliminate_decoded {m} {Γ : Context m} (w n : Fin m) (r : Formula m) (hd : Derives Γ (decoded w n))
    (hc : Derives (Context.add (decodedBody w n) (Context.image Formula.raise (Context.image Formula.raise Γ))) r.raise.raise) : Derives Γ r := by
  change Derives Γ (.ex (.ex (decodedBody w n))) at hd
  apply Derives.exE hd
  apply Derives.exE (p := decodedBody w n) (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro r (hr | ⟨s, hs, he⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr hs, he⟩

theorem valid_of_decoded {m} {Γ : Context m} (w n : Fin m) (hd : Derives Γ (decoded w n)) : Derives Γ (valid w n) := by
  let D := decodedBody w n
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_decoded w n _ hd
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hout := StructuralListLengthBasic.valid_of_length _ _ _ (.conjR (.conjL hD))
  simpa only [Formula.raise, valid_rename] using hout

theorem exists_decoded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (valid w n)) : Derives Γ (decoded w n) := by
  have hl := StructuralListLengthBasic.exists_length w n hv
  let L := (Formula.mem (Fin.last m) w.castSucc).conj (hasLength w.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add L (Context.image Formula.raise Γ)
  change Derives Γ (.ex L) at hl
  apply Derives.exE (p := L) hl
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ L
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw L
  have hL : Derives Ξ L := .hyp (Or.inl rfl)
  have hg := StructuralListFieldGraphFiber.exists_unique hZ1 w.castSucc n.castSucc (Fin.last m) hw1 (.conjL hL)
  let G := (fields w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj (.all
    ((graph w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))).imp
      (.equal (Fin.last (m+2)) (Fin.last (m+1)).castSucc)))
  let Δ := Context.add G (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex G) at hg
  apply Derives.exE (p := G) hg
  have hL2 : Derives Δ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [L, Formula.raise, Formula.rename, hasLength_rename] using under hL G
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hout := intro_decoded _ _ _ _ (.conjL hL2) (.conjR hL2) (.conjL hG)
  simpa only [Formula.raise, decoded_rename] using hout

theorem decoded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((valid w n).iff (decoded w n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact exists_decoded (ZFContext.add hZ _) w n (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact valid_of_decoded w n (.hyp (Or.inl rfl))

theorem unique_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l k g h : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (hasLength w n l)) (hk : Derives Γ (hasLength w n k))
    (hg : Derives Γ (fields w n l g)) (hh : Derives Γ (fields w n k h)) : Derives Γ ((Formula.equal l k).conj (.equal g h)) := by
  have heq := StructuralListLengthUnique.unique hZ w n l k hw hl hk
  have hhSame := graph_domain_subst w n k l h (eq_symm heq) (.conjL (.conjR hh))
  exact .conjI heq (StructuralListFieldGraphFiber.unique hZ w n l g h (.conjL (.conjR hg)) hhSame)

theorem at_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (hasLength w n l)) : Derives Γ (fieldsFiber w n l) :=
  StructuralListFieldGraphFiber.exists_unique hZ w n l hw (StructuralListLengthBasic.length_member w n l hl)
end PPAC.Migration.Internal.StructuralListFieldDecode
