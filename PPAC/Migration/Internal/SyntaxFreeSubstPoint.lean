import PPAC.Migration.Internal.SyntaxFreeSubstSyntax

/-! 替换项字段与 free 索引的双向关系在全部内部域点上实际存在唯一。 -/
namespace PPAC.Migration.Internal.SyntaxFreeSubstPoint
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxFreeSubstSyntax
open SyntaxVariableSyntax (code code_rename)
open SyntaxTermSyntax (branch branch_rename)
open SyntaxIndexMapSyntax (indexMap indexMap_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem code_subst_output {m} {Γ : Context m} (w j t u : Fin m)
    (he : Derives Γ (.equal t u)) (hc : Derives Γ (code false w j t)) : Derives Γ (code false w j u) := by
  let P := code false w.castSucc j.castSucc (Fin.last m)
  exact of_eq (by simp only [P, Formula.instantiate, code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc))

theorem code_subst_index {m} {Γ : Context m} (w j k t : Fin m)
    (he : Derives Γ (.equal j k)) (hc : Derives Γ (code false w j t)) : Derives Γ (code false w k t) := by
  let P := code false w.castSucc (Fin.last m) t.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc))

theorem decoded_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a i j k : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functionOn f a))
    (hj : Derives Γ (decodedValue w f i j)) (hk : Derives Γ (decodedValue w f i k)) : Derives Γ (.equal j k) := by
  let B := (edge f.castSucc i.castSucc (Fin.last m)).conj (code false w.castSucc j.castSucc (Fin.last m))
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hj
  have hk1 : Derives Ξ (decodedValue w.castSucc f.castSucc i.castSucc k.castSucc) :=
    of_eq (decodedValue_rename w f i k Fin.castSucc) (under hk B)
  let C := (edge f.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).conj (code false w.castSucc.castSucc k.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add C (Context.image Formula.raise Ξ)
  apply Derives.exE (p := C) hk1
  have hZ2 := ZFContext.under (ZFContext.under hZ B) C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw B) C)
  have hf2 : Derives Δ (functionOn f.castSucc.castSucc a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, functionOn_rename]) (under (under hf B) C)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hb2 : Derives Δ ((edge f.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc).conj (code false w.castSucc.castSucc j.castSucc.castSucc (Fin.last m).castSucc)) := of_eq (by simp only [B, Formula.raise, Formula.rename, edge_rename, code_rename]) (under hB C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have he := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ2).base.extensionality hf2 (.conjL hb2) (.conjL hC)
  have hc := code_subst_output _ _ _ _ he (.conjR hb2)
  exact SyntaxVariableDecode.index_eq hZ2 false _ _ _ _ hw2 hc (.conjR hC)

theorem encoded_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a i j k : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functionOn f a))
    (hj : Derives Γ (encodedValue w f i j)) (hk : Derives Γ (encodedValue w f i k)) : Derives Γ (.equal j k) := by
  let B := (edge f.castSucc i.castSucc (Fin.last m)).conj (code false w.castSucc (Fin.last m) j.castSucc)
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hj
  have hk1 : Derives Ξ (encodedValue w.castSucc f.castSucc i.castSucc k.castSucc) :=
    of_eq (encodedValue_rename w f i k Fin.castSucc) (under hk B)
  let C := (edge f.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).conj (code false w.castSucc.castSucc (Fin.last (m+1)) k.castSucc.castSucc)
  let Δ := Context.add C (Context.image Formula.raise Ξ)
  apply Derives.exE (p := C) hk1
  have hZ2 := ZFContext.under (ZFContext.under hZ B) C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw B) C)
  have hf2 : Derives Δ (functionOn f.castSucc.castSucc a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, functionOn_rename]) (under (under hf B) C)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hb2 : Derives Δ ((edge f.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc).conj (code false w.castSucc.castSucc (Fin.last m).castSucc j.castSucc.castSucc)) := of_eq (by simp only [B, Formula.raise, Formula.rename, edge_rename, code_rename]) (under hB C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have he := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ2).base.extensionality hf2 (.conjL hb2) (.conjL hC)
  have hc := code_subst_index _ _ _ _ he (.conjR hb2)
  exact SyntaxVariables.unique hZ2 false _ _ _ _ hw2 hc (.conjR hC)

theorem decoded_target {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c i j : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (termGraph w f a c))
    (hd : Derives Γ (decodedValue w f i j)) : Derives Γ (.mem j c) := by
  let B := (edge f.castSucc i.castSucc (Fin.last m)).conj (code false w.castSucc j.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hd
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hf1 : Derives Δ (termGraph w.castSucc f.castSucc a.castSucc c.castSucc) := of_eq (termGraph_rename w f a c Fin.castSucc) (under hf B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hb := Derives.impE (values_at _ _ _ _ _ (.conjR (.conjR hf1))) (.conjL hB)
  exact SyntaxTermBranches.member (ZFContext.under hZ B) false _ _ _ _ hw1 (.conjR hB) hb

theorem encoded_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r i t : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (encodedValue w r i t)) : Derives Γ (.mem t w) := by
  let B := (edge r.castSucc i.castSucc (Fin.last m)).conj (code false w.castSucc (Fin.last m) t.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  exact SyntaxVariableDecode.range (ZFContext.under hZ B) false _ _ _ hw1
    (Derives.conjR (Derives.hyp (Or.inl rfl) : Derives Δ B))

theorem encoded_free {m} {Γ : Context m} (w r a c i t : Fin m)
    (hr : Derives Γ (indexMap w r a c)) (he : Derives Γ (encodedValue w r i t)) : Derives Γ (branch false w c t) := by
  let B := (edge r.castSucc i.castSucc (Fin.last m)).conj (code false w.castSucc (Fin.last m) t.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hr1 : Derives Δ (indexMap w.castSucc r.castSucc a.castSucc c.castSucc) := of_eq (indexMap_rename w r a c Fin.castSucc) (under hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hj := SyntaxIndexMapSyntax.edge_target _ _ _ _ _ _ hr1 (.conjL hB)
  exact of_eq (branch_rename false w c t Fin.castSucc).symm (SyntaxTermSyntax.intro_branch false _ _ _ _ hj (.conjR hB))

theorem decoded_exists {m} {Γ : Context m} (w f a c i : Fin m)
    (hf : Derives Γ (termGraph w f a c)) (hi : Derives Γ (.mem i a)) :
    Derives Γ (.ex (decodedValue w.castSucc f.castSucc i.castSucc (Fin.last m))) := by
  have he := GraphProperties.output_exists f a i (.conjL (.conjL (.conjR hf))) hi
  let T := edge f.castSucc i.castSucc (Fin.last m)
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hf1 : Derives Ξ (termGraph w.castSucc f.castSucc a.castSucc c.castSucc) := of_eq (termGraph_rename w f a c Fin.castSucc) (under hf T)
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hb := Derives.impE (values_at _ _ _ _ _ (.conjR (.conjR hf1))) hT
  let J := SyntaxTermSyntax.branchWitness false w.castSucc c.castSucc (Fin.last m)
  let Δ := Context.add J (Context.image Formula.raise Ξ)
  apply SyntaxTermSyntax.eliminate_branch false w.castSucc c.castSucc (Fin.last m) _ hb
  have ht2 : Derives Δ (edge f.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) := of_eq (edge_rename _ _ _ Fin.castSucc) (under hT J)
  have hJ : Derives Δ J := .hyp (Or.inl rfl)
  have hd := intro_decoded _ _ _ _ _ ht2 (.conjR hJ)
  have ho : Derives Δ (.ex (decodedValue w.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc (Fin.last (m+2)))) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, decodedValue_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hd
  exact of_eq (by simp only [Formula.raise, Formula.rename, decodedValue_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

theorem encoded_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c i : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (indexMap w r a c)) (hi : Derives Γ (.mem i a)) :
    Derives Γ (.ex (encodedValue w.castSucc r.castSucc i.castSucc (Fin.last m))) := by
  have he := GraphProperties.output_exists r a i (.conjL (.conjR hr)) hi
  let J := edge r.castSucc i.castSucc (Fin.last m)
  let Ξ := Context.add J (Context.image Formula.raise Γ)
  apply Derives.exE (p := J) he
  have hZ1 := ZFContext.under hZ J
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw J)
  have hr1 : Derives Ξ (indexMap w.castSucc r.castSucc a.castSucc c.castSucc) := of_eq (indexMap_rename w r a c Fin.castSucc) (under hr J)
  have hJ : Derives Ξ J := .hyp (Or.inl rfl)
  have hc := SyntaxIndexMapSyntax.edge_target _ _ _ _ _ _ hr1 hJ
  have hj := StructuralListTraceOrder.member_member hZ1 _ _ _ hw1 (.conjR (.conjL hr1)) hc
  let T := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (code false w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add T (Context.image Formula.raise Ξ)
  apply Derives.exE (p := T) (SyntaxVariables.exists_code hZ1 false _ _ hw1 hj)
  have he2 : Derives Δ (edge r.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) := of_eq (edge_rename _ _ _ Fin.castSucc) (under hJ T)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hd := intro_encoded _ _ _ _ _ he2 (.conjR hT)
  have ho : Derives Δ (.ex (encodedValue w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc (Fin.last (m+2)))) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, encodedValue_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hd
  exact of_eq (by simp only [Formula.raise, Formula.rename, encodedValue_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

end PPAC.Migration.Internal.SyntaxFreeSubstPoint
