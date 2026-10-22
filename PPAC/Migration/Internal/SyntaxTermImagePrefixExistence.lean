import PPAC.Migration.Internal.SyntaxTermImagePrefixUnique

/-! 每个内部后继源域索引实际有头槽扩展值，允许原源域为空。 -/
namespace PPAC.Migration.Internal.SyntaxTermImagePrefixExistence
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxTermImagePrefixSyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem point_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c d z A i : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (imageMap w f a c d)) (hA : Derives Γ (successor A a))
    (hi : Derives Γ (.mem i A)) : Derives Γ (.ex (value f.castSucc a.castSucc z.castSucc i.castSucc (Fin.last m))) := by
  have hANat := OmegaStructureAlgebra.successor_member w A a (ZFContext.arithmetic hZ).base.extensionality hw (.conjL hf) hA
  have hiNat := StructuralListTraceOrder.member_member hZ w i A hw hANat hi
  have hd := OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw
  apply Derives.disjE (OmegaStructureAlgebra.decomposition_at w i hd hiNat)
  · apply Derives.exI z
    have hv : Derives (Context.add (empty i) Γ) (value f a z i z) := .disjL (.conjI (.hyp (Or.inl rfl)) (.eqRefl z))
    exact of_eq (by simp only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hv
  · let V := OmegaStructureSyntax.predecessor w i
    let K := (Formula.mem (Fin.last m) w.castSucc).conj (successor i.castSucc (Fin.last m))
    let Ξ := Context.add K (Context.image Formula.raise (Context.add V Γ))
    apply Derives.exE (p := K) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ V) K
    have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw V) K)
    have hf1 : Derives Ξ (imageMap w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc) := of_eq (imageMap_rename w f a c d Fin.castSucc) (under (add hf V) K)
    have hA1 : Derives Ξ (successor A.castSucc a.castSucc) := of_eq (successor_rename A a Fin.castSucc) (under (add hA V) K)
    have hK : Derives Ξ K := .hyp (Or.inl rfl)
    have hk := SyntaxIndexLiftOrder.predecessor_member hZ1 _ _ _ _ _ hw1 (.conjL hf1) hA1 (under (add hi V) K) (.conjR hK)
    let Q := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    let Δ := Context.add Q (Context.image Formula.raise Ξ)
    apply Derives.exE (p := Q) (GraphProperties.output_exists _ _ _ (SyntaxTermImageSyntax.image_function _ _ _ _ _ hf1) hk)
    have hk2 : Derives Δ (.mem (Fin.last m).castSucc a.castSucc.castSucc) := under hk Q
    have hi2 : Derives Δ (successor i.castSucc.castSucc (Fin.last m).castSucc) := of_eq (successor_rename i.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hK) Q)
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    have hv := intro_shifted f.castSucc.castSucc a.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hk2 hi2 hQ
    have hval : Derives Δ (value f.castSucc.castSucc a.castSucc.castSucc z.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))) := .disjR hv
    have ho : Derives Δ (.ex (value f.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc (Fin.last (m+2)))) := by
      apply Derives.exI (Fin.last (m+1))
      exact of_eq (by simp only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hval
    exact of_eq (by simp only [Formula.raise, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

end PPAC.Migration.Internal.SyntaxTermImagePrefixExistence
