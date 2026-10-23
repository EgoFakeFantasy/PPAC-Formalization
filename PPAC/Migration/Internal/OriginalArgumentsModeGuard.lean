import PPAC.Migration.Internal.OriginalArgumentsExpr

/-! 原nilArguments的mode<4守卫在内部Num0/Num3上实际消去，保留自然赋值。 -/
namespace PPAC.Migration.Internal.OriginalArgumentsModeGuard
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectSyntaxTransform (nilArguments)

theorem nil_guard {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool) (w : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0))) :
    Derives Γ (HornRuleSyntax.guards nilArguments.guards w env) := by
  have he := SyntaxNumerals.exists_numeral hZ 4 w hw
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 4 (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 3 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 3 w env Fin.castSucc) (under hn B)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0).castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under hm B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hlt : OriginalScalarClasses.mode three < 4 := by cases three <;> decide
  have hmem := SyntaxNumerals.less hZ1 (OriginalScalarClasses.mode three) 4 hlt (env 0).castSucc (Fin.last m) hm1 (.conjR hB)
  have hv : Derives Δ (graph (.var (0 : Fin 3)) w.castSucc (fun i => (env i).castSucc) (env 0).castSucc) := .conjI (environmentNat_at _ _ hn1 0) (.eqRefl _)
  have hg := Derives.impE (.conjR (HornRuleValue.guard_at hZ1 (.var (0 : Fin 3)) (.literal 4) w.castSucc (env 0).castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 hv (.conjR hB))) hmem
  have ho : Derives Δ (HornRuleSyntax.guards nilArguments.guards w.castSucc (fun i => (env i).castSucc)) := .conjI hg HornRuleSyntax.truth_proved
  exact of_eq (HornRuleSyntax.guards_rename nilArguments.guards w env Fin.castSucc).symm ho

end PPAC.Migration.Internal.OriginalArgumentsModeGuard
