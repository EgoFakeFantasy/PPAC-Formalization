import PPAC.Migration.Internal.ProofTreeRootForward

/-! 零自由变量与精确结论字段实际构造原根行及闭轨迹；不假设根已有效。 -/
namespace PPAC.Migration.Internal.ProofTreeRootBackward
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open ProofTreeBranchConstruction (shape)

theorem matrix_backward {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (kind : Fin 6)
    (w code conclusion : Fin m) (env : Fin ((shape kind).extra+2) → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (ProofTreeEntrySyntax.node test w code)) (hm : Derives Γ (ProofTreeRootSyntax.matrix kind w code conclusion env)) :
    Derives Γ (ProofTreeEntrySyntax.root test w code conclusion) := by
  let s := shape kind
  have hnat := Derives.conjL hm
  have hcode := ProofTreeConstructorFacts.range hZ (s.extra+2) s.tag w code env hw (.conjL (.conjR hm))
  have hc := mem_subst (.conjR (.conjR (.conjR hm))) (environmentNat_at w env hnat 1)
  have hi := SyntaxForestSyntax.intro_inputs 2 w (SetLanguage.args2 code conclusion) (fun i => Fin.cases hcode (fun j => Fin.cases hc (fun t => Fin.elim0 t) j) i)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 2 1 w.castSucc (SetLanguage.args2 code.castSucc conclusion.castSucc) (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxConstructors.exists_constructor hZ 2 1 w (SetLanguage.args2 code conclusion) hw hi)
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hm1 := of_eq (ProofTreeRootSyntax.matrix_rename kind w code conclusion env Fin.castSucc) (under hm B)
  have hn1 := of_eq (ProofTreeEntryFacts.node_rename test w code Fin.castSucc) (under hn B)
  have he := Derives.conjR (Derives.conjR (Derives.conjR hm1))
  have hnat1 := Derives.conjL hm1
  have hp := Derives.impE (.conjR (ProofTreeBranchHead.payload_iff hZ1 s w.castSucc code.castSucc (fun i => (env i).castSucc) hw1 hnat1)) (.conjL (.conjR hm1))
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hh : Derives Δ (graph (ObjectProofTree.branch s true).head w.castSucc (fun i => (env i).castSucc) (Fin.last m)) := by
    apply Derives.impE (.conjR (HornExprConstructor.constructor_iff hZ1 2 1 (SetLanguage.args2 (ObjectProofTree.payload s) (.var 1)) w.castSucc (Fin.last m) (fun i => (env i).castSucc) (SetLanguage.args2 code.castSucc conclusion.castSucc) hw1 hnat1 ?_)) (.conjR hB)
    intro i
    refine Fin.cases hp (fun j => ?_) i
    refine Fin.cases ?_ (fun t => Fin.elim0 t) j
    exact .conjI (environmentNat_at w.castSucc (fun i => (env i).castSucc) hnat1 1) (eq_symm he)
  have hg := Derives.impE (.conjR (ProofTreeZeroGuard.guard_iff hZ1 0 w.castSucc (fun i => (env i).castSucc) hw1 hnat1)) (.conjL (.conjR (.conjR hm1)))
  have hpre := Derives.impE (.conjR (ProofTreeBranchHead.premise_iff test hZ1 s w.castSucc code.castSucc (fun i => (env i).castSucc) hw1 hnat1 hp)) hn1
  have hmat : Derives Δ (ProofTreeTracedStep.matrix test (ObjectProofTree.branch s true) w.castSucc (Fin.last m) (fun i => (env i).castSucc)) :=
    .conjI hh (.conjI (.conjI hg HornRuleSyntax.truth_proved) (.conjI hpre HornRuleSyntax.truth_proved))
  have hl := ProofTreeRootLocal.constructor_one test hZ1 2 w.castSucc (Fin.last m) (SetLanguage.args2 code.castSucc conclusion.castSucc) hw1 (.conjR hB)
  have ht := ProofTreeBranchConstruction.intro_branch test hZ1 kind true w.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hnat1 hmat hl
  have ho : Derives Δ (ProofTreeEntrySyntax.root test w.castSucc code.castSucc conclusion.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [ProofTreeEntrySyntax.root, Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
      ProofTreeTraceSyntax.condition_rename, ProofTreeEntryFacts.args2_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI (.conjR hB) ht
  exact of_eq (ProofTreeEntryFacts.root_rename test w code conclusion Fin.castSucc).symm ho

theorem branch_backward {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (kind : Fin 6)
    (w code conclusion : Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (ProofTreeEntrySyntax.node test w code))
    (hb : Derives Γ (ProofTreeRootSyntax.branch kind w code conclusion)) : Derives Γ (ProofTreeEntrySyntax.root test w code conclusion) := by
  let k := (shape kind).extra+2
  let B := ProofTreeRootSyntax.body kind w code conclusion
  let Δ := Context.add B (raisedContext k Γ)
  apply HornBinderRules.eliminate_many k B _ hb
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hwN := of_eq (omega_rename w (old k)) (HornBinderRules.under_body k hw B)
  have hnN := of_eq (ProofTreeEntryFacts.node_rename test w code (old k)) (HornBinderRules.under_body k hn B)
  have ho := matrix_backward test (HornBinderRules.zf_body k hZ B) kind (old k w) (old k code) (old k conclusion) (slot k) hwN hnN hB
  exact of_eq (ProofTreeEntryFacts.root_rename test w code conclusion (old k)).symm ho

theorem root_backward {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w code conclusion : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (ProofTreeRootSyntax.normalized test w code conclusion)) :
    Derives Γ (ProofTreeEntrySyntax.root test w code conclusion) := by
  apply ProofTreeRootSyntax.disjoin_elim (ProofTreeRootSyntax.kinds.map (fun kind => ProofTreeRootSyntax.branch kind w code conclusion)) _ (.conjR hn)
  intro q hq
  obtain ⟨kind,_,rfl⟩ := List.mem_map.mp hq
  apply Derives.impI
  exact branch_backward test (ZFContext.add hZ _) kind w code conclusion (add hw _) (add (.conjL hn) _) (.hyp (Or.inl rfl))

theorem root_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w code conclusion : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((ProofTreeEntrySyntax.root test w code conclusion).iff (ProofTreeRootSyntax.normalized test w code conclusion)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact ProofTreeRootForward.root_forward test (ZFContext.add hZ _) w code conclusion (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact root_backward test (ZFContext.add hZ _) w code conclusion (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.ProofTreeRootBackward
