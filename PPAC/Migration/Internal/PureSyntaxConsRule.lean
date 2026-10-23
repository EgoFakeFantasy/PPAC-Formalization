import PPAC.Migration.Internal.PureSyntaxNilComplete
import PPAC.Migration.Internal.PureSyntaxTraceMerge

/-! 原cons规则实际引用头项和尾参数列；合并真实轨迹后构造父行的接受证书。 -/
namespace PPAC.Migration.Internal.PureSyntaxConsRule
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

def fields : Fin 4 → Expr 5 := PureSyntaxTrace.four (.var 0) (.var 1) (.succ (.var 2)) (ObjectTermSyntax.cons (.var 3) (.var 4))
def headFields : Fin 3 → Expr 5 := Fin.cases (.var 0) (Fin.cases (.var 1) (Fin.cases (.var 3) Fin.elim0))
def tailFields : Fin 4 → Expr 5 := PureSyntaxTrace.four (.var 0) (.var 1) (.var 2) (.var 4)

theorem actual_head : ObjectTermSyntax.consRule.head = Expr.node (.literal 1) (List.ofFn fields) := rfl

theorem rule_mem : ObjectTermSyntax.consRule ∈ PureSyntaxRules.rules :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem matrix_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w k n r R p q : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hk : Derives Γ (successor k (env 2))) (hc : Derives Γ (StructuralListSyntax.consCode w (env 3) (env 4) n))
    (hr : Derives Γ (PureSyntaxTrace.argumentRow w (env 0) (env 1) k n r))
    (hp : Derives Γ (PureSyntaxTrace.termRow w (env 0) (env 1) (env 3) p))
    (hq : Derives Γ (PureSyntaxTrace.argumentRow w (env 0) (env 1) (env 2) (env 4) q))
    (hpm : Derives Γ (.mem p R)) (hqm : Derives Γ (.mem q R)) :
    Derives Γ (HornRuleSyntax.matrix ObjectTermSyntax.consRule w r R env) := by
  have hv (i : Fin 5) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  have gs : ∀ j : Fin 4, Derives Γ (graph (fields j) w env (PureSyntaxTrace.four (env 0) (env 1) k n j)) := by
    intro j
    refine Fin.cases (hv 0) (fun i => ?_) j
    refine Fin.cases (hv 1) (fun l => ?_) i
    refine Fin.cases (intro_succ (.var 2) w k (env 2) env (hv 2) hk) (fun t => ?_) l
    refine Fin.cases ?_ (fun z => Fin.elim0 z) t
    exact HornExprStructural.cons_graph (.var 3) (.var 4) w (env 3) (env 4) n env (hv 3) (hv 4) hc
  have gh := HornExprForest.constructor_graph 4 1 fields w r env (PureSyntaxTrace.four (env 0) (env 1) k n) gs hr
  have gp := HornExprForest.constructor_graph 3 0 headFields w p env (SyntaxAtomSyntax.three (env 0) (env 1) (env 3))
    (fun j => Fin.cases (hv 0) (fun i => Fin.cases (hv 1) (fun l => Fin.cases (hv 3) (fun z => Fin.elim0 z) l) i) j) hp
  have gq := HornExprForest.constructor_graph 4 1 tailFields w q env (PureSyntaxTrace.four (env 0) (env 1) (env 2) (env 4))
    (fun j => Fin.cases (hv 0) (fun i => Fin.cases (hv 1) (fun l => Fin.cases (hv 2) (fun t => Fin.cases (hv 4) (fun z => Fin.elim0 z) t) l) i) j) hq
  have pp := Derives.impE (.conjR (HornRuleValue.premise_at hZ _ w R p env hw hn gp)) hpm
  have pq := Derives.impE (.conjR (HornRuleValue.premise_at hZ _ w R q env hw hn gq)) hqm
  exact .conjI (of_eq (congrArg (fun e => graph e w env r) actual_head.symm) gh)
    (.conjI HornRuleSyntax.truth_proved (.conjI pp (.conjI pq HornRuleSyntax.truth_proved)))

theorem application_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w k n r R p q : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hk : Derives Γ (successor k (env 2))) (hc : Derives Γ (StructuralListSyntax.consCode w (env 3) (env 4) n))
    (hr : Derives Γ (PureSyntaxTrace.argumentRow w (env 0) (env 1) k n r))
    (hp : Derives Γ (PureSyntaxTrace.termRow w (env 0) (env 1) (env 3) p))
    (hq : Derives Γ (PureSyntaxTrace.argumentRow w (env 0) (env 1) (env 2) (env 4) q))
    (hpm : Derives Γ (.mem p R)) (hqm : Derives Γ (.mem q R)) :
    Derives Γ (HornApplicationSyntax.application ObjectTermSyntax.consRule w r R) := by
  have hm := matrix_complete hZ w k n r R p q env hw hn hk hc hr hp hq hpm hqm
  have hb := HornExprBounds.intro_environmentBound r env (fun i =>
    HornExprBounds.variable_bound hZ ObjectTermSyntax.consRule.head i (PureSyntaxRules.head_variables _ rule_mem i) w r env hw hn (.conjL hm))
  exact HornApplicationRules.intro_application _ w r R env hn hb hm

theorem condition_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w k n r p q : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hk : Derives Γ (successor k (env 2))) (hc : Derives Γ (StructuralListSyntax.consCode w (env 3) (env 4) n))
    (hr : Derives Γ (PureSyntaxTrace.argumentRow w (env 0) (env 1) k n r))
    (hp : Derives Γ (PureSyntaxTrace.termRow w (env 0) (env 1) (env 3) p))
    (hq : Derives Γ (PureSyntaxTrace.argumentRow w (env 0) (env 1) (env 2) (env 4) q))
    (hcp : Derives Γ (PureSyntaxTrace.condition w p)) (hcq : Derives Γ (PureSyntaxTrace.condition w q)) :
    Derives Γ (PureSyntaxTrace.condition w r) := by
  let B := PureSyntaxTraceMerge.pairWitness w.castSucc p.castSucc q.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (PureSyntaxTraceMerge.two_conditions hZ w p q hcp hcq)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 5 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 5 w env Fin.castSucc) (under hn B)
  have hk1 : Derives Δ (successor k.castSucc (env 2).castSucc) := of_eq (successor_rename _ _ Fin.castSucc) (under hk B)
  have hc1 : Derives Δ (StructuralListSyntax.consCode w.castSucc (env 3).castSucc (env 4).castSucc n.castSucc) := of_eq (StructuralListSyntax.consCode_rename _ _ _ _ Fin.castSucc) (under hc B)
  have hr1 : Derives Δ (PureSyntaxTrace.argumentRow w.castSucc (env 0).castSucc (env 1).castSucc k.castSucc n.castSucc r.castSucc) := of_eq (PureSyntaxTrace.argumentRow_rename _ _ _ _ _ _ Fin.castSucc) (under hr B)
  have hp1 : Derives Δ (PureSyntaxTrace.termRow w.castSucc (env 0).castSucc (env 1).castSucc (env 3).castSucc p.castSucc) := of_eq (PureSyntaxTrace.termRow_rename _ _ _ _ _ Fin.castSucc) (under hp B)
  have hq1 : Derives Δ (PureSyntaxTrace.argumentRow w.castSucc (env 0).castSucc (env 1).castSucc (env 2).castSucc (env 4).castSucc q.castSucc) := of_eq (PureSyntaxTrace.argumentRow_rename _ _ _ _ _ _ Fin.castSucc) (under hq B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hm := matrix_complete hZ1 _ _ _ _ _ _ _ _ hw1 hn1 hk1 hc1 hr1 hp1 hq1 (.conjL (.conjR (.conjR hB))) (.conjR (.conjR (.conjR hB)))
  have ha := application_complete hZ1 _ _ _ _ _ _ _ _ hw1 hn1 hk1 hc1 hr1 hp1 hq1 (.conjL (.conjR (.conjR hB))) (.conjR (.conjR (.conjR hB)))
  have hnat := HornExprRange.range hZ1 ObjectTermSyntax.consRule.head w.castSucc r.castSucc (fun i => (env i).castSucc) hw1 hn1 (.conjL hm)
  have ho := PureSyntaxTraceExtension.condition hZ1 w.castSucc (Fin.last m) r.castSucc (.conjL hB) hnat (.conjL (.conjR hB))
    (HornStepSyntax.rule_intro PureSyntaxRules.rules ObjectTermSyntax.consRule rule_mem _ _ _ ha)
  exact of_eq (PureSyntaxTrace.condition_rename w r Fin.castSucc).symm ho

end PPAC.Migration.Internal.PureSyntaxConsRule
