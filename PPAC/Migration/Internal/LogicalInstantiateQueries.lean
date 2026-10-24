import PPAC.Migration.Internal.InstantiateTopFormulaOperation
import PPAC.Migration.Internal.OriginalTransformExprQuery
import PPAC.Migration.Internal.PureSyntaxQueryTyping
import YesMetaZFC.Automation.ObjectLogicalAxiom

/-! 原逻辑模式的bound1公式／bound0项／mode2实例化三个实际查询，固定字段位置保持外部有限参数。 -/
namespace PPAC.Migration.Internal.LogicalInstantiateQueries
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

def fields {a} (bound : Nat) (free input : Fin a) : Fin 3 → Expr a :=
  Fin.cases (.literal bound) (Fin.cases (.var free) (Fin.cases (.var input) Fin.elim0))

def formulaQuery {a} (free input : Fin a) : Expr a :=
  (ObjectLogicalAxiom.grammar false (.literal 1) (.var free) (.var input)).2

def termQuery {a} (free input : Fin a) : Expr a :=
  (ObjectLogicalAxiom.grammar true (.literal 0) (.var free) (.var input)).2

def transformQuery {a} (parameter input output : Fin a) : Expr a :=
  (ObjectLogicalAxiom.transform 2 (.var parameter) (.var input) (.var output)).2

theorem formula_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (free input : Fin a)
    (w z A : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat a w env)) (hz : Derives Γ (empty z)) (hA : Derives Γ (successor A z)) :
    Derives Γ ((PureSyntaxExprQuery.query (formulaQuery free input) w env).iff (FormulaCodeSyntax.formulaCode w (env input) A (env free))) := by
  have hv (i : Fin a) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  have hOne := SyntaxNumeralSyntax.intro_succ 0 A z hz hA
  exact PureSyntaxQueryTyping.formula_iff hZ (fields 1 free input) w A (env free) (env input) env hw hn
    (fun i => Fin.cases hOne (fun j => Fin.cases (hv free) (fun k => Fin.cases (hv input) (fun v => Fin.elim0 v) k) j) i)

theorem term_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (free input : Fin a)
    (w z : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat a w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((PureSyntaxExprQuery.query (termQuery free input) w env).iff (SyntaxTermSyntax.term w z (env free) (env input))) := by
  have hv (i : Fin a) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  exact PureSyntaxQueryTyping.term_iff hZ (fields 0 free input) w z (env free) (env input) env hw hn
    (fun i => Fin.cases hz (fun j => Fin.cases (hv free) (fun k => Fin.cases (hv input) (fun v => Fin.elim0 v) k) j) i)

theorem transform_at_mode {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (parameter input output : Fin a)
    (w z mode : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat a w env)) (hz : Derives Γ (empty z))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode)) :
    Derives Γ ((OriginalTransformExprQuery.query (transformQuery parameter input output) w env).iff
      (OriginalTransformRowSyntax.run 3 w mode z (env parameter) (env input) (env output))) := by
  have hv (i : Fin a) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  have hq := OriginalTransformExprQuery.constructor_query_iff hZ 5 3
    (HornRowFields.five (.literal 2) (.literal 0) (.var parameter) (.var input) (.var output)) w env
    (HornRowFields.five mode z (env parameter) (env input) (env output)) hw hn
    (fun i => Fin.cases hm (fun j => Fin.cases hz (fun k => Fin.cases (hv parameter) (fun l => Fin.cases (hv input) (fun _ => hv output) l) k) j) i)
  change Derives Γ ((OriginalTransformExprQuery.query (transformQuery parameter input output) w env).iff
    (OriginalTransformExprQuery.rowQuery 5 3 w (HornRowFields.five mode z (env parameter) (env input) (env output)))) at hq
  simpa only [OriginalTransformExprQuery.rowQuery, OriginalTransformRowSyntax.run, OriginalTransformRowSyntax.row, FreeWeakenResultSyntax.five_map] using hq

theorem typed_transform_at_mode {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (free parameter input output : Fin a)
    (w z A mode : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat a w env)) (hz : Derives Γ (empty z)) (hA : Derives Γ (successor A z))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hp : Derives Γ (SyntaxTermSyntax.term w z (env free) (env parameter)))
    (hf : Derives Γ (FormulaCodeSyntax.formulaCode w (env input) A (env free))) :
    Derives Γ ((OriginalTransformExprQuery.query (transformQuery parameter input output) w env).iff
      (SyntaxTopFormulaSyntax.instantiated w z (env free) A (env parameter) (env input) (env output))) :=
  SyntaxTypeLocalTransfer.iff_trans (transform_at_mode hZ parameter input output w z mode env hw hn hz hm)
    (InstantiateTopFormulaOperation.run_iff hZ w mode z (env parameter) (env free) A (env input) (env output)
      hw hm hz (.conjI hp hA) hf)

theorem typed_transform_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (free parameter input output : Fin a)
    (w z A : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat a w env)) (hz : Derives Γ (empty z)) (hA : Derives Γ (successor A z))
    (hp : Derives Γ (SyntaxTermSyntax.term w z (env free) (env parameter)))
    (hf : Derives Γ (FormulaCodeSyntax.formulaCode w (env input) A (env free))) :
    Derives Γ ((OriginalTransformExprQuery.query (transformQuery parameter input output) w env).iff
      (SyntaxTopFormulaSyntax.instantiated w z (env free) A (env parameter) (env input) (env output))) := by
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 2 (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxNumerals.exists_numeral hZ 2 w hw)
  have lift {p : Formula m} (h : Derives Γ p) : Derives Δ p.raise := under h B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
  have hn1 := of_eq (environmentNat_rename a w env Fin.castSucc) (lift hn)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
  have hA1 := of_eq (successor_rename A z Fin.castSucc) (lift hA)
  have hp1 := of_eq (SyntaxTermSyntax.term_rename w z (env free) (env parameter) Fin.castSucc) (lift hp)
  have hf1 := of_eq (FormulaCodeSyntax.formulaCode_rename w (env input) A (env free) Fin.castSucc) (lift hf)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := typed_transform_at_mode (ZFContext.under hZ B) free parameter input output w.castSucc z.castSucc A.castSucc (Fin.last m) (fun i => (env i).castSucc)
    hw1 hn1 hz1 hA1 (.conjR hB) hp1 hf1
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, OriginalTransformExprQuery.query_rename, SyntaxTopFormulaSyntax.instantiated_rename]) ho

end PPAC.Migration.Internal.LogicalInstantiateQueries
