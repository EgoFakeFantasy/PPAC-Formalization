import PPAC.Migration.Internal.OriginalTermTraceVariable
import PPAC.Migration.Internal.TermTransformProgramCorrectness
import PPAC.Migration.Internal.IndexTermImageCodeFields
import PPAC.Migration.Internal.SyntaxFreeShiftFiber

/-! 实际恒等／位移项像列表字段对应原变量值；完整内部图和码由原对象存在块对齐。 -/
namespace PPAC.Migration.Internal.OriginalTermImageFields
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem edge_output_subst {m} {Γ : Context m} (r i j k : Fin m) (he : Derives Γ (.equal j k))
    (hh : Derives Γ (edge r i j)) : Derives Γ (edge r i k) := by
  let P := edge r.castSucc i.castSucc (Fin.last m)
  have h0 : P.instantiate j = edge r i j := by simp only [P, Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate k = edge r i k := by simp only [P, Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem diagonal_edge {m} {Γ : Context m} (w r a i : Fin m)
    (hm : Derives Γ (SyntaxIndexMapSyntax.indexMap w r a a)) (hd : Derives Γ (SyntaxRenameTermIdentity.diagonal r))
    (hi : Derives Γ (.mem i a)) : Derives Γ (edge r i i) := by
  have he := GraphProperties.output_exists r a i (.conjL (.conjR hm)) hi
  let B := edge r.castSucc i.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hd1 : Derives Δ (SyntaxRenameTermIdentity.diagonal r.castSucc) := of_eq (SyntaxRenameTermIdentity.diagonal_rename r Fin.castSucc) (under hd B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have eq := SyntaxRenameTermIdentity.diagonal_at _ _ _ hd1 hB
  exact of_eq (edge_rename r i i Fin.castSucc).symm (edge_output_subst _ _ _ _ (eq_symm eq) hB)

theorem code_iff_equal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w i n q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxVariableSyntax.code bound w i n)) :
    Derives Γ ((SyntaxVariableSyntax.code bound w i q).iff (.equal q n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact SyntaxVariables.unique (ZFContext.add hZ _) bound w i q n (add hw _) (.hyp (Or.inl rfl)) (add hn _)
  · apply Derives.impI
    exact HornVariableValue.code_output_subst bound w i n q (eq_symm (.hyp (Or.inl rfl))) (add hn _)

theorem identity_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c I R i q : Fin m)
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hR : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c)) (hi : Derives Γ (.mem i a)) :
    Derives Γ ((StructuralListFieldSyntax.field w R i q).iff (SyntaxVariableSyntax.code true w i q)) := by
  let C := IndexTermImageCodeSyntax.body true w I R a a c
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 C _ hR
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hI2 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w.castSucc.castSucc a.castSucc.castSucc I.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityCode_rename]) (SyntaxRenameBinders.under_2 hI C)
  have hR2 : Derives Δ (IndexTermImageCodeSyntax.converted true w.castSucc.castSucc I.castSucc.castSucc R.castSucc.castSucc a.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, IndexTermImageCodeSyntax.converted_rename]) (SyntaxRenameBinders.under_2 hR C)
  have hi2 : Derives Δ (.mem i.castSucc.castSucc a.castSucc.castSucc) := SyntaxRenameBinders.under_2 hi C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hd := SyntaxIdentityCode.at_graph hZ2 _ _ _ (Fin.last m).castSucc hI2 (.conjL hC)
  have he := diagonal_edge _ _ _ _ (.conjR (.conjL hC)) hd hi2
  have hf := IndexTermImageCodeFields.at_edge hZ2 true w.castSucc.castSucc I.castSucc.castSucc R.castSucc.castSucc a.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc i.castSucc.castSucc i.castSucc.castSucc q.castSucc.castSucc hR2 (.conjL hC) he
  have ho := TermQuotationBinderFields.drop_member _ _ _ hi2 hf
  simpa only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, SyntaxVariableSyntax.code_rename] using ho

theorem shift_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B J S i q : Fin m)
    (hJ : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (hS : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B)) (hi : Derives Γ (.mem i b)) :
    Derives Γ ((StructuralListFieldSyntax.field w S i q).iff (FreeWeakenValueSyntax.shifted w i q)) := by
  let C := IndexTermImageCodeSyntax.body false w J S b a B
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 C _ hS
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hJ2 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc J.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftCode_rename]) (SyntaxRenameBinders.under_2 hJ C)
  have hS2 : Derives Δ (IndexTermImageCodeSyntax.converted false w.castSucc.castSucc J.castSucc.castSucc S.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, IndexTermImageCodeSyntax.converted_rename]) (SyntaxRenameBinders.under_2 hS C)
  have hi2 : Derives Δ (.mem i.castSucc.castSucc b.castSucc.castSucc) := SyntaxRenameBinders.under_2 hi C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hm := SyntaxFreeShiftCode.at_graph hZ2 _ _ _ _ (Fin.last m).castSucc hJ2 (.conjL hC)
  have hg := SyntaxFreeShiftGraph.to_graph _ _ _ _ hm
  have he := InsertExistence.exists_insert i.castSucc.castSucc i.castSucc.castSucc (ZFContext.arithmetic hZ2).base.pairing (ZFContext.arithmetic hZ2).base.union
  let T := successor (Fin.last (m+2)) i.castSucc.castSucc.castSucc
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) he
  have hZ3 := ZFContext.under hZ2 T
  have hi3 : Derives Ξ (.mem i.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc) := under hi2 T
  have hS3 : Derives Ξ (IndexTermImageCodeSyntax.converted false w.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc) := of_eq
    (IndexTermImageCodeSyntax.converted_rename _ _ _ _ _ _ _ Fin.castSucc) (under hS2 T)
  have henc : Derives Ξ (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc b.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc) := of_eq
    (SyntaxMapCodeSyntax.encoded_rename _ _ _ _ _ Fin.castSucc) (under (.conjL hC) T)
  have hg3 : Derives Ξ (SyntaxFreeShiftSyntax.graph b.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) := of_eq
    (SyntaxFreeShiftSyntax.graph_rename _ _ Fin.castSucc) (under hg T)
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hedge := Derives.impE (.conjR (SyntaxFreeShiftGraph.edge_iff _ _ _ _ hg3)) (.conjI hi3 hT)
  have hf := IndexTermImageCodeFields.at_edge hZ3 false w.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc i.castSucc.castSucc.castSucc (Fin.last (m+2)) q.castSucc.castSucc.castSucc hS3 henc hedge
  have hcode := TermQuotationBinderFields.drop_member _ _ _ hi3 hf
  have hvalue := FreeWeakenValue.at_successor hZ3 w.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc (Fin.last (m+2)) hT
  have ho := SyntaxTypeLocalTransfer.iff_trans hcode (.conjI (.conjR hvalue) (.conjL hvalue))
  simpa only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, FreeWeakenValueSyntax.shifted_rename] using ho

end PPAC.Migration.Internal.OriginalTermImageFields
