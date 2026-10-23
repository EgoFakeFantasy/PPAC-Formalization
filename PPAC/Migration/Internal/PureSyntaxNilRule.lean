import PPAC.Migration.Internal.PureSyntaxTermMatrix
import PPAC.Migration.Internal.TypedArgumentListCases

/-! 原nil规则的真实四字段矩阵与纯空参数列；所有元数据为内部候选。 -/
namespace PPAC.Migration.Internal.PureSyntaxNilRule
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

def fields : Fin 4 → Expr 2 := PureSyntaxTrace.four (.var 0) (.var 1) (.literal 0) (Expr.list [])

theorem actual_head : ObjectTermSyntax.nilRule.head = Expr.node (.literal 1) (List.ofFn fields) := rfl

theorem rule_mem : ObjectTermSyntax.nilRule ∈ PureSyntaxRules.rules :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem nil_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w y : Fin m) (env : Fin a → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env)) :
    Derives Γ ((graph (Expr.list []) w env y).iff (StructuralListSyntax.nilCode w y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := graph (Expr.list []) w env y
    have he := SyntaxForests.exists_forest (ZFContext.add hZ E) 0 w Fin.elim0 (add hw E) (.eqRefl w)
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListSyntax.nilCode w.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) he
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hn1 : Derives Δ (environmentNat a w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename a w env Fin.castSucc) (under (add hn E) B)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hy1 : Derives Δ (graph (Expr.list []) w.castSucc (fun i => (env i).castSucc) y.castSucc) := of_eq (graph_rename _ w y env Fin.castSucc) (under hE B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have heq := HornExprUnique.unique (ZFContext.under (ZFContext.add hZ E) B) (Expr.list []) _ _ _ _ hw1 hn1 hy1
      (HornExprStructural.nil_graph _ _ _ (.conjR hB))
    have hn0 := Derives.conjR hB
    have heq0 := eq_symm heq
    have hout : Derives Δ (StructuralListSyntax.nilCode w.castSucc y.castSucc) := by
      let P := StructuralListSyntax.nilCode w.castSucc.castSucc (Fin.last (m+1))
      have h0 : P.instantiate (Fin.last m) = StructuralListSyntax.nilCode w.castSucc (Fin.last m) := by simp only [P, Formula.instantiate, StructuralListSyntax.nilCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
      have h1 : P.instantiate y.castSucc = StructuralListSyntax.nilCode w.castSucc y.castSucc := by simp only [P, Formula.instantiate, StructuralListSyntax.nilCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
      exact of_eq h1 (Derives.eqSubst P heq0 (of_eq h0.symm hn0))
    exact of_eq (StructuralListSyntax.nilCode_rename w y Fin.castSucc).symm hout
  · apply Derives.impI
    exact HornExprStructural.nil_graph w y env (.hyp (Or.inl rfl))

theorem matrix_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f k n r R : Fin m)
    (env : Fin 2 → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 2 w env))
    (hr : Derives Γ (PureSyntaxTrace.argumentRow w b f k n r))
    (hm : Derives Γ (HornRuleSyntax.matrix ObjectTermSyntax.nilRule w r R env)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w k b f n) := by
  have hg := Derives.conjL hm
  rw [actual_head] at hg
  have h0 := HornNodeFields.field_4 hZ 1 fields w r env (PureSyntaxTrace.four b f k n) 0 hw hn hg hr
  have h1 := HornNodeFields.field_4 hZ 1 fields w r env (PureSyntaxTrace.four b f k n) 1 hw hn hg hr
  have h2 := HornNodeFields.field_4 hZ 1 fields w r env (PureSyntaxTrace.four b f k n) 2 hw hn hg hr
  have h3 := HornNodeFields.field_4 hZ 1 fields w r env (PureSyntaxTrace.four b f k n) 3 hw hn hg hr
  have hc : Derives Γ (SyntaxTermSyntax.contexts w b f) := .conjI
    (mem_subst (eq_symm (.conjR h0)) (environmentNat_at w env hn 0))
    (mem_subst (eq_symm (.conjR h1)) (environmentNat_at w env hn 1))
  have hnil := Derives.impE (.conjL (nil_iff hZ w n env hw hn)) h3
  exact TypedArgumentListConstruction.nil_list hZ w k b f n hw h2 hc hnil

theorem matrix_complete {m} {Γ : Context m} (w k n r R : Fin m) (env : Fin 2 → Fin m)
    (hn : Derives Γ (environmentNat 2 w env)) (hk : Derives Γ (empty k))
    (hnil : Derives Γ (StructuralListSyntax.nilCode w n))
    (hr : Derives Γ (PureSyntaxTrace.argumentRow w (env 0) (env 1) k n r)) :
    Derives Γ (HornRuleSyntax.matrix ObjectTermSyntax.nilRule w r R env) := by
  have hs : ∀ j : Fin 4, Derives Γ (graph (fields j) w env (PureSyntaxTrace.four (env 0) (env 1) k n j)) := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact .conjI (environmentNat_at w env hn 0) (.eqRefl _)
    · refine Fin.cases ?_ (fun l => ?_) i
      · exact .conjI (environmentNat_at w env hn 1) (.eqRefl _)
      · refine Fin.cases ?_ (fun z => ?_) l
        · exact hk
        · refine Fin.cases ?_ (fun z => Fin.elim0 z) z
          exact HornExprStructural.nil_graph w n env hnil
  have hg := HornExprForest.constructor_graph 4 1 fields w r env (PureSyntaxTrace.four (env 0) (env 1) k n) hs hr
  exact .conjI (of_eq (congrArg (fun e => graph e w env r) actual_head.symm) hg)
    (.conjI HornRuleSyntax.truth_proved HornRuleSyntax.truth_proved)

theorem application_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w k n r R : Fin m)
    (env : Fin 2 → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 2 w env))
    (hk : Derives Γ (empty k)) (hnil : Derives Γ (StructuralListSyntax.nilCode w n))
    (hr : Derives Γ (PureSyntaxTrace.argumentRow w (env 0) (env 1) k n r)) :
    Derives Γ (HornApplicationSyntax.application ObjectTermSyntax.nilRule w r R) := by
  have hm := matrix_complete w k n r R env hn hk hnil hr
  have hb := HornExprBounds.intro_environmentBound r env (fun i =>
    HornExprBounds.variable_bound hZ ObjectTermSyntax.nilRule.head i (PureSyntaxRules.head_variables _ rule_mem i) w r env hw hn (.conjL hm))
  exact HornApplicationRules.intro_application _ w r R env hn hb hm

theorem application_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f k n r R : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (PureSyntaxTrace.argumentRow w b f k n r))
    (ha : Derives Γ (HornApplicationSyntax.application ObjectTermSyntax.nilRule w r R)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w k b f n) := by
  let B := HornApplicationSyntax.body ObjectTermSyntax.nilRule w r R
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornApplicationRules.eliminate_application ObjectTermSyntax.nilRule w r R _ ha
  have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hr1 : Derives Δ (PureSyntaxTrace.argumentRow (old 2 w) (old 2 b) (old 2 f) (old 2 k) (old 2 n) (old 2 r)) := of_eq (PureSyntaxTrace.argumentRow_rename w b f k n r (old 2)) (HornBinderRules.under_body 2 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := matrix_sound (HornBinderRules.zf_body 2 hZ B) _ _ _ _ _ _ _ (slot 2) hw1 (.conjL hB) hr1 (.conjR (.conjR hB))
  exact of_eq (SyntaxMixedImageCodeSyntax.termList_rename w k b f n (old 2)).symm ht

end PPAC.Migration.Internal.PureSyntaxNilRule
