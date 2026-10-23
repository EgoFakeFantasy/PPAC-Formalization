import PPAC.Migration.Internal.SyntaxVariableImageSyntax

/-! 变量项码像关系的实际类型、存在和单值性；所有索引及项码均为内部对象见证。 -/
namespace PPAC.Migration.Internal.SyntaxVariableImagePoint
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxVariableImageSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem code_subst_index {m} {Γ : Context m} (bound : Bool) (w j q k : Fin m)
    (he : Derives Γ (.equal j k)) (hc : Derives Γ (SyntaxVariableSyntax.code bound w j q)) :
    Derives Γ (SyntaxVariableSyntax.code bound w k q) := by
  let P := SyntaxVariableSyntax.code bound w.castSucc (Fin.last m) q.castSucc
  have e0 : P.instantiate j = SyntaxVariableSyntax.code bound w j q := by
    simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate k = SyntaxVariableSyntax.code bound w k q := by
    simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

theorem target_type {m} {Γ : Context m} (bound : Bool) (w r c d i q : Fin m)
    (hv : Derives Γ (value bound w r c d i q)) : Derives Γ (SyntaxTermSyntax.term w c d q) := by
  let B := body bound w r c d i q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hv
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (SyntaxTermSyntax.term_rename w c d q Fin.castSucc).symm (.conjR (.conjR hB))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r a c d i q v : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functionOn r a))
    (hq : Derives Γ (value bound w r c d i q)) (hv : Derives Γ (value bound w r c d i v)) : Derives Γ (.equal q v) := by
  let B := body bound w r c d i q
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hq
  have hv1 : Derives Ξ (value bound w.castSucc r.castSucc c.castSucc d.castSucc i.castSucc v.castSucc) :=
    of_eq (value_rename bound w r c d i v Fin.castSucc) (under hv B)
  let A := body bound w.castSucc r.castSucc c.castSucc d.castSucc i.castSucc v.castSucc
  let Δ := Context.add A (Context.image Formula.raise Ξ)
  apply Derives.exE (p := A) hv1
  have hZ2 := ZFContext.under (ZFContext.under hZ B) A
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw B) A)
  have hf2 : Derives Δ (functionOn r.castSucc.castSucc a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, functionOn_rename]) (under (under hf B) A)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hb2 : Derives Δ ((edge r.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc).conj
      ((SyntaxVariableSyntax.code bound w.castSucc.castSucc (Fin.last m).castSucc q.castSucc.castSucc).conj
        (SyntaxTermSyntax.term w.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc q.castSucc.castSucc))) :=
    of_eq (by simp only [B, body, Formula.raise, Formula.rename, edge_rename, SyntaxVariableSyntax.code_rename, SyntaxTermSyntax.term_rename]) (under hB A)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have he := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ2).base.extensionality hf2 (.conjL hb2) (.conjL hA)
  have hc := code_subst_index bound w.castSucc.castSucc (Fin.last m).castSucc q.castSucc.castSucc (Fin.last (m+1)) he (.conjL (.conjR hb2))
  exact SyntaxVariables.unique hZ2 bound w.castSucc.castSucc (Fin.last (m+1)) q.castSucc.castSucc v.castSucc.castSucc hw2 hc (.conjL (.conjR hA))

theorem exists_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r a c d i : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input bound w r a c d)) (hm : Derives Γ (.mem i a)) :
    Derives Γ (.ex (value bound w.castSucc r.castSucc c.castSucc d.castSucc i.castSucc (Fin.last m))) := by
  let T := edge r.castSucc i.castSucc (Fin.last m)
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (GraphProperties.output_exists r a i (.conjL (.conjR (.conjR hi))) hm)
  have hZ1 := ZFContext.under hZ T
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hi1 : Derives Ξ (input bound w.castSucc r.castSucc a.castSucc c.castSucc d.castSucc) := of_eq (input_rename bound w r a c d Fin.castSucc) (under hi T)
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hj := SyntaxIndexMapSyntax.edge_target w.castSucc r.castSucc a.castSucc (SyntaxTermSyntax.limit bound c.castSucc d.castSucc) i.castSucc (Fin.last m) (.conjR hi1) hT
  let N := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    ((SyntaxVariableSyntax.code bound w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
      (SyntaxTermSyntax.term w.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1))))
  let Δ := Context.add N (Context.image Formula.raise Ξ)
  apply Derives.exE (p := N) (SyntaxTerms.exists_at hZ1 bound w.castSucc c.castSucc d.castSucc (Fin.last m) hw1 (.conjI (.conjL hi1) hj))
  have he2 : Derives Δ (edge r.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [T, Formula.raise, edge_rename]) (under hT N)
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hv := intro_value bound w.castSucc.castSucc r.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc he2 (.conjL (.conjR hN)) (.conjR (.conjR hN))
  have ho : Derives Δ (.ex (value bound w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc (Fin.last (m+2)))) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hv
  exact of_eq (by simp only [Formula.raise, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

theorem source_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r a c d i q : Fin m)
    (hi : Derives Γ (input bound w r a c d)) (hv : Derives Γ (value bound w r c d i q)) : Derives Γ (.mem i a) := by
  let B := body bound w r c d i q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hv
  have hi1 : Derives Δ (input bound w.castSucc r.castSucc a.castSucc c.castSucc d.castSucc) := of_eq (input_rename bound w r a c d Fin.castSucc) (under hi B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact GraphProperties.domain_of_edge _ _ _ _ (ZFContext.arithmetic (ZFContext.under hZ B)).base.extensionality (.conjL (.conjR (.conjR hi1))) (.conjL hB)
end PPAC.Migration.Internal.SyntaxVariableImagePoint
