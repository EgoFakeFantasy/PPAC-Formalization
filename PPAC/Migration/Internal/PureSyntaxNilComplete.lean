import PPAC.Migration.Internal.PureSyntaxNilRule

/-! 空参数列的原nil规则及真实闭轨迹在对象ZF内实际构造。 -/
namespace PPAC.Migration.Internal.PureSyntaxNilComplete
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation

theorem intro_arguments {m} {Γ : Context m} (w b f k n r : Fin m)
    (hr : Derives Γ (PureSyntaxTrace.argumentRow w b f k n r)) (hc : Derives Γ (PureSyntaxTrace.condition w r)) :
    Derives Γ (PureSyntaxTrace.arguments w b f k n) := by
  apply Derives.exI r
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, PureSyntaxTrace.argumentRow_rename, PureSyntaxTrace.condition_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr hc)

theorem checked_nil {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f k n : Fin m)
    (hw : Derives Γ (omega w)) (hk : Derives Γ (empty k)) (hctx : Derives Γ (SyntaxTermSyntax.contexts w b f))
    (hnil : Derives Γ (StructuralListSyntax.nilCode w n)) : Derives Γ (PureSyntaxTrace.arguments w b f k n) := by
  have hkn := OmegaStructureAlgebra.zero_member w k (ZFContext.arithmetic hZ).base.extensionality hw hk
  have hnn := StructuralNil.range hZ w n hw hnil
  have hi := SyntaxForestSyntax.intro_inputs 4 w (PureSyntaxTrace.four b f k n)
    (fun i => Fin.cases (.conjL hctx) (fun j => Fin.cases (.conjR hctx) (fun l => Fin.cases hkn (fun t => Fin.cases hnn (fun z => Fin.elim0 z) t) l) j) i)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj
    (PureSyntaxTrace.argumentRow w.castSucc b.castSucc f.castSucc k.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxConstructors.exists_constructor hZ 4 1 w (PureSyntaxTrace.four b f k n) hw hi)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hk1 : Derives Δ (empty k.castSucc) := of_eq (empty_rename k Fin.castSucc) (under hk B)
  have hnil1 : Derives Δ (StructuralListSyntax.nilCode w.castSucc n.castSucc) := of_eq (StructuralListSyntax.nilCode_rename w n Fin.castSucc) (under hnil B)
  have hctx1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc b.castSucc f.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w b f Fin.castSucc) (under hctx B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  let env : Fin 2 → Fin (m+1) := Fin.cases b.castSucc (fun _ => f.castSucc)
  have hnat : Derives Δ (HornExprSyntax.environmentNat 2 w.castSucc env) :=
    HornApplicationRules.intro_nat w.castSucc env (fun i => Fin.cases (.conjL hctx1) (fun j => Fin.cases (.conjR hctx1) (fun z => Fin.elim0 z) j) i)
  have ha := PureSyntaxNilRule.application_complete hZ1 w.castSucc k.castSucc n.castSucc (Fin.last m) w.castSucc env hw1 hnat hk1 hnil1 (.conjR hB)
  have hc := PureSyntaxTraceRules.premise_free_condition hZ1 ObjectTermSyntax.nilRule PureSyntaxNilRule.rule_mem rfl w.castSucc (Fin.last m) (.conjL hB) ha
  exact of_eq (PureSyntaxTrace.arguments_rename w b f k n Fin.castSucc).symm
    (intro_arguments _ _ _ _ _ _ (.conjR hB) hc)

theorem typed_nil_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f k n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k b f n))
    (hnil : Derives Γ (StructuralListSyntax.nilCode w n)) : Derives Γ (PureSyntaxTrace.arguments w b f k n) := by
  have hp := Derives.impE (.conjL (TypedArgumentListCases.nil_iff hZ w k b f n hw hnil)) ht
  exact checked_nil hZ w b f k n hw (.conjL hp) (.conjR hp) hnil

end PPAC.Migration.Internal.PureSyntaxNilComplete
