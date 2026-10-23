import PPAC.Migration.Internal.PureSyntaxMembershipType

/-! 原成员规则的实际kind1前提恢复内部长度2列表及真实二项有类型森林。 -/
namespace PPAC.Migration.Internal.PureSyntaxMembershipPremise
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

def fields : Fin 4 → Expr 3 := PureSyntaxTrace.four (.var 0) (.var 1) (.literal 2) (.var 2)
def head : Expr 3 := Expr.node (.literal 1) (List.ofFn fields)

theorem at_numeral {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R len : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hl : Derives Γ (SyntaxNumeralSyntax.numeral 2 len)) (hs : Derives Γ (RestrictionSyntax.subset R w))
    (hc : Derives Γ (PureSyntaxTrace.closed w R)) (hp : Derives Γ (HornRuleSyntax.premise head w R env)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w len (env 0) (env 1) (env 2)) := by
  let B := (graph head w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (.mem (Fin.last m) R.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hp
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 3 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 3 w env Fin.castSucc) (under hn B)
  have hl1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 len.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename 2 len Fin.castSucc) (under hl B)
  have hs1 : Derives Δ (RestrictionSyntax.subset R.castSucc w.castSucc) := of_eq (RestrictionSyntax.subset_rename R w Fin.castSucc) (under hs B)
  have hc1 : Derives Δ (PureSyntaxTrace.closed w.castSucc R.castSucc) := of_eq (PureSyntaxTrace.closed_rename w R Fin.castSucc) (under hc B)
  have hv (i : Fin 3) : Derives Δ (graph (.var i) w.castSucc (fun j => (env j).castSucc) (env i).castSucc) := .conjI (environmentNat_at _ _ hn1 i) (.eqRefl _)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := HornExprConstructor.constructor_iff hZ1 4 1 fields w.castSucc (Fin.last m) (fun i => (env i).castSucc)
    (PureSyntaxTrace.four (env 0).castSucc (env 1).castSucc len.castSucc (env 2).castSucc) hw1 hn1
    (fun i => Fin.cases (hv 0) (fun j => Fin.cases (hv 1) (fun k => Fin.cases hl1 (fun l => Fin.cases (hv 2) (fun z => Fin.elim0 z) l) k) j) i)
  have hr := Derives.impE (.conjL hi) (.conjL hB)
  have hcond := PureSyntaxTrace.intro_condition _ _ _ (.conjI hs1 (.conjI (.conjR hB) hc1))
  have ht := PureSyntaxArgumentInduction.checked_sound hZ1 _ _ _ _ _ hw1
    (PureSyntaxNilComplete.intro_arguments _ _ _ _ _ _ hr hcond)
  exact of_eq (SyntaxMixedImageCodeSyntax.termList_rename w len (env 0) (env 1) (env 2) Fin.castSucc).symm ht

theorem pair_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hp : Derives Γ (HornRuleSyntax.premise head w R env)) : Derives Γ (ArgumentPairOutput.output w (env 0) (env 1) (env 2)) := by
  let L := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 2 (Fin.last m))
  let Δ := Context.add L (Context.image Formula.raise Γ)
  apply Derives.exE (p := L) (SyntaxNumerals.exists_numeral hZ 2 w hw)
  have hZ1 := ZFContext.under hZ L
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw L)
  have hn1 : Derives Δ (environmentNat 3 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 3 w env Fin.castSucc) (under hn L)
  have hs1 : Derives Δ (RestrictionSyntax.subset R.castSucc w.castSucc) := of_eq (RestrictionSyntax.subset_rename R w Fin.castSucc) (under hs L)
  have hc1 : Derives Δ (PureSyntaxTrace.closed w.castSucc R.castSucc) := of_eq (PureSyntaxTrace.closed_rename w R Fin.castSucc) (under hc L)
  have hp1 : Derives Δ (HornRuleSyntax.premise head w.castSucc R.castSucc (fun i => (env i).castSucc)) := of_eq (HornRuleSyntax.premise_rename head w R env Fin.castSucc) (under hp L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have ht := at_numeral hZ1 _ _ (Fin.last m) _ hw1 hn1 (.conjR hL) hs1 hc1 hp1
  exact of_eq (ArgumentPairOutput.output_rename w (env 0) (env 1) (env 2) Fin.castSucc).symm
    (ArgumentPairOutput.exists_output hZ1 w.castSucc (Fin.last m) (env 0).castSucc (env 1).castSucc (env 2).castSucc hw1 (.conjR hL) ht)

theorem construct {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R len p : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) (hl : Derives Γ (SyntaxNumeralSyntax.numeral 2 len))
    (hr : Derives Γ (PureSyntaxTrace.argumentRow w (env 0) (env 1) len (env 2) p)) (hm : Derives Γ (.mem p R)) :
    Derives Γ (HornRuleSyntax.premise head w R env) := by
  have hv (i : Fin 3) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  have hg := HornExprForest.constructor_graph 4 1 fields w p env (PureSyntaxTrace.four (env 0) (env 1) len (env 2))
    (fun i => Fin.cases (hv 0) (fun j => Fin.cases (hv 1) (fun k => Fin.cases hl (fun l => Fin.cases (hv 2) (fun z => Fin.elim0 z) l) k) j) i) hr
  exact .impE (.conjR (HornRuleValue.premise_at hZ head w R p env hw hn hg)) hm

end PPAC.Migration.Internal.PureSyntaxMembershipPremise
