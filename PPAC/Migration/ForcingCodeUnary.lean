import PPAC.Migration.ForcingCodeUnique
import PPAC.Migration.Internal.StructuralListTraceOrder

/-! Actual atomic/negative/forall/exists computation laws. All target fragments
are the existing compiler definitions. Reuse the completed selectors and
original recursion; never accept a supplied history or local answer. -/
namespace PPAC.Migration.ForcingCodeUnary
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 16384
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- The original negation, universal, existential tags. -/
def tag : Fin 3 → Nat := Fin.cases 4 (Fin.cases 9 (fun _ => 10))
def childScope {m} (kind : Fin 3) (a A : Fin m) : Fin m := Fin.cases a (fun _ => A) kind
private def advance (kind : Fin 3) : Bool := Fin.cases false (fun _ => true) kind
private theorem scope_map {m l} (kind : Fin 3) (a A : Fin m) (r : Fin m → Fin l) :
    r (childScope kind a A) = childScope kind (r a) (r A) := by
  have hk : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega
  rcases hk with rfl | rfl | rfl <;> rfl

def output {k m} (kind : Fin 3) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w a A B C f j N Q : Fin m) : Formula m :=
  Fin.cases (ForcingNegCode.compiled R w a A f j N Q)
    (Fin.cases (ForcingLogicalCode.universal R H w a A B C f j N Q) (fun _ => ForcingExistCode.compiled R H w a A B C f j N Q)) kind
theorem output_rename {k m l} (kind : Fin 3) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w a A B C f j N Q : Fin m) (r : Fin m → Fin l) :
    (output kind R H w a A B C f j N Q).rename r = output kind R H (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) (r Q) := by
  have hk : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega
  rcases hk with rfl | rfl | rfl
  · exact ForcingNegCode.compiled_rename R w a A f j N Q r
  · exact ForcingLogicalCode.universal_rename R H w a A B C f j N Q r
  · exact ForcingExistCode.compiled_rename R H w a A B C f j N Q r

private def selected {k m} (kind : Fin 3) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C g n Q : Fin m) : Formula m :=
  Fin.cases (ForcingCodeStep.negative R H w z f j a A B C g n Q)
    (Fin.cases (ForcingCodeStep.universal R H w z f j a A B C g n Q) (fun _ => ForcingCodeStep.existential R H w z f j a A B C g n Q)) kind
private def data {k m} (kind : Fin 3) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C g n Q x X : Fin m) : Formula m :=
  (FormulaCodeRecursiveSyntax.singleFields (tag kind) (advance kind) w a z x n).conj
    ((ForcingCodeStep.read w g x (childScope kind a A) f X).conj (output kind R H w a A B C f j X Q))
private theorem data_rename {k m l} (kind : Fin 3) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C g n Q x X : Fin m) (r : Fin m → Fin l) :
    (data kind R H w z f j a A B C g n Q x X).rename r = data kind R H (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r g) (r n) (r Q) (r x) (r X) := by
  simp only [data, Formula.rename, FormulaCodeRecursiveSyntax.singleFields_rename, ForcingCodeStep.read_rename, output_rename, scope_map]
private def body {k m} (kind : Fin 3) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C g n Q : Fin m) : Formula (m+2) :=
  data kind R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 g) (old 2 n) (old 2 Q) (slot 2 0) (slot 2 1)
private theorem selected_eq {k m} (kind : Fin 3) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C g n Q : Fin m) :
    selected kind R H w z f j a A B C g n Q = existsMany 2 (body kind R H w z f j a A B C g n Q) := by
  have hk : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega
  rcases hk with rfl | rfl | rfl <;> rfl
private theorem select_case {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C g n Q x : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (tag kind) w x n))
    (hs : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C g n Q)) : Derives Γ (selected kind R H w z f j a A B C g n Q) := by
  have hk : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega
  rcases hk with rfl | rfl | rfl
  · exact ForcingCodeStepUnique.select_negative hZ R H w z f j a A B C g n Q x hw hc hs
  · exact ForcingCodeStepUnique.select_universal hZ R H w z f j a A B C g n Q x hw hc hs
  · exact ForcingCodeStepUnique.select_existential hZ R H w z f j a A B C g n Q x hw hc hs
private theorem read_subst {m} {Γ : Context m} (w g x a f Q y : Fin m)
    (he : Derives Γ (.equal x y)) (hr : Derives Γ (ForcingCodeStep.read w g x a f Q)) : Derives Γ (ForcingCodeStep.read w g y a f Q) := by
  let P := ForcingCodeStep.read w.castSucc g.castSucc (Fin.last m) a.castSucc f.castSucc Q.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, ForcingCodeStep.read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, ForcingCodeStep.read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr))

private theorem at_data {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C g n Q x N u U : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (tag kind) w x n))
    (hg : Derives Γ (ForcingCodeRecursion.graph R H w z f j g n))
    (hN : Derives Γ (ForcingCodeRecursion.compiled R H w z f j (childScope kind a A) x N))
    (hd : Derives Γ (data kind R H w z f j a A B C g n Q u U)) : Derives Γ (output kind R H w a A B C f j N Q) := by
  have he := SyntaxLogicalFields.single_fields hZ (tag kind) w u x n hw (.conjL (.conjL hd)) hc
  have hb := SyntaxLogicalFields.single_bound hZ (tag kind) w x n hw hc
  have hr := read_subst w g u (childScope kind a A) f U x he (.conjL (.conjR hd))
  have hU := ForcingCodeRecursion.read_to_compiled hZ R H w z f j g n (childScope kind a A) x U (NaturalOrderBasic.ordinal hZ w n hw hn) hb hg hr
  have eq := ForcingCodeUnique.unique hZ R H w z f j (childScope kind a A) x U N hw (StructuralListTraceOrder.member_member hZ w x n hw hn hb) hU hN
  let P := output kind R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc (Fin.last m) Q.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, output_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P eq (of_eq (by simp only [P, Formula.instantiate, output_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR (.conjR hd))))
private theorem at_case {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C g n Q x N : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (tag kind) w x n))
    (hg : Derives Γ (ForcingCodeRecursion.graph R H w z f j g n))
    (hN : Derives Γ (ForcingCodeRecursion.compiled R H w z f j (childScope kind a A) x N))
    (hd : Derives Γ (selected kind R H w z f j a A B C g n Q)) : Derives Γ (output kind R H w a A B C f j N Q) := by
  let E := body kind R H w z f j a A B C g n Q
  let Δ := Context.add E (raisedContext 2 Γ)
  have he : Derives Γ (existsMany 2 E) := of_eq (selected_eq kind R H w z f j a A B C g n Q) hd
  apply HornBinderRules.eliminate_many 2 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (output_rename kind R H w a A B C f j N Q (old 2)).symm
    (at_data (HornBinderRules.zf_body 2 hZ E) kind R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C)
      (old 2 g) (old 2 n) (old 2 Q) (old 2 x) (old 2 N) (slot 2 0) (slot 2 1)
      (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E)) (HornBinderRules.under_body 2 hn E)
      (of_eq (SyntaxLogicalSyntax.singleCode_rename (tag kind) w x n (old 2)) (HornBinderRules.under_body 2 hc E))
      (of_eq (ForcingCodeRecursion.graph_rename R H w z f j g n (old 2)) (HornBinderRules.under_body 2 hg E))
      (of_eq (by simp only [ForcingCodeRecursion.compiled_rename, scope_map]) (HornBinderRules.under_body 2 hN E)) hE)
private theorem at_graph {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C g n Q x N : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (tag kind) w x n))
    (hg : Derives Γ (ForcingCodeRecursion.graph R H w z f j g n))
    (hQ : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n Q))
    (hN : Derives Γ (ForcingCodeRecursion.compiled R H w z f j (childScope kind a A) x N)) : Derives Γ (output kind R H w a A B C f j N Q) := by
  have hs := ForcingCodeUnique.compiled_step hZ R H w z f j n g a A B C Q hw (NaturalOrderBasic.ordinal hZ w n hw hn) hA hB hC hg hQ
  exact at_case hZ kind R H w z f j a A B C g n Q x N hw hn hc hg hN (select_case hZ kind R H w z f j a A B C g n Q x hw hc (.conjR hs))

/-- Exact negation/forall/exists compilation on independently generated child
outputs at their ORIGINAL scopes (a for negation, A=a+1 for binders). -/
theorem unary {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C n Q x N : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (tag kind) w x n))
    (hQ : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n Q))
    (hN : Derives Γ (ForcingCodeRecursion.compiled R H w z f j (childScope kind a A) x N)) : Derives Γ (output kind R H w a A B C f j N Q) := by
  let E := ForcingCodeRecursion.graph R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) n.castSucc
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (ForcingCodeRecursion.exists_graph hZ R H w z f j n (NaturalOrderBasic.ordinal hZ w n hw hn))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (output_rename kind R H w a A B C f j N Q Fin.castSucc).symm
    (at_graph (ZFContext.under hZ E) kind R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc
      (Fin.last m) n.castSucc Q.castSucc x.castSucc N.castSucc (of_eq (omega_rename w Fin.castSucc) (under hw E)) (under hn E)
      (of_eq (successor_rename A a Fin.castSucc) (under hA E)) (of_eq (successor_rename B A Fin.castSucc) (under hB E)) (of_eq (successor_rename C B Fin.castSucc) (under hC E))
      (of_eq (SyntaxLogicalSyntax.singleCode_rename (tag kind) w x n Fin.castSucc) (under hc E)) hE
      (of_eq (ForcingCodeRecursion.compiled_rename R H w z f j a n Q Fin.castSucc) (under hQ E))
      (of_eq (by simp only [ForcingCodeRecursion.compiled_rename, scope_map]) (under hN E)))

/-- All four atomic constructors use the exact existing atomic compiler. -/
theorem atomic {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C n Q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hc : Derives Γ (SyntaxAtomSyntax.atomic w a z n)) (hQ : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n Q)) :
    Derives Γ (ForcingAtomCode.compiled R w a z n Q) := by
  let E := ForcingCodeRecursion.graph R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) n.castSucc
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (ForcingCodeRecursion.exists_graph hZ R H w z f j n (NaturalOrderBasic.ordinal hZ w n hw hn))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hs := ForcingCodeUnique.compiled_step (ZFContext.under hZ E) R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc (Fin.last m)
    a.castSucc A.castSucc B.castSucc C.castSucc Q.castSucc hw1
    (of_eq (OrdinalSyntax.ordinal_rename n Fin.castSucc) (under (NaturalOrderBasic.ordinal hZ w n hw hn) E))
    (of_eq (successor_rename A a Fin.castSucc) (under hA E)) (of_eq (successor_rename B A Fin.castSucc) (under hB E))
    (of_eq (successor_rename C B Fin.castSucc) (under hC E)) hE
    (of_eq (ForcingCodeRecursion.compiled_rename R H w z f j a n Q Fin.castSucc) (under hQ E))
  exact of_eq (ForcingAtomCode.compiled_rename R w a z n Q Fin.castSucc).symm
    (.conjR (ForcingCodeStepUnique.select_atomic (ZFContext.under hZ E) R H w.castSucc z.castSucc f.castSucc j.castSucc
      a.castSucc A.castSucc B.castSucc C.castSucc (Fin.last m) n.castSucc Q.castSucc hw1
      (of_eq (SyntaxAtomSyntax.atomic_rename w a z n Fin.castSucc) (under hc E)) (.conjR hs)))

def input {k m} (kind : Fin 3) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C n Q x N : Fin m) : Formula m :=
  (omega w).conj ((Formula.mem n w).conj ((successor A a).conj ((successor B A).conj ((successor C B).conj
    ((SyntaxLogicalSyntax.singleCode (tag kind) w x n).conj ((ForcingCodeRecursion.compiled R H w z f j a n Q).conj
      (ForcingCodeRecursion.compiled R H w z f j (childScope kind a A) x N)))))))
def sentence {k m} (kind : Fin 3) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C n Q x N : Fin m) : Source.Sentence :=
  ((input kind R H w z f j a A B C n Q x N).imp (output kind R H w a A B C f j N Q)).close
theorem kernel_certificate {k m} (kind : Fin 3) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C n Q x N : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence kind R H w z f j a A B C n Q x N)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input kind R H w z f j a A B C n Q x N
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact unary (ZFContext.add (ZFContext.source_ZF m) E) kind R H w z f j a A B C n Q x N (.conjL h) (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h))) (.conjL (.conjR (.conjR (.conjR h)))) (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h)))))) (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))

def atomicInput {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C n Q : Fin m) : Formula m :=
  (omega w).conj ((Formula.mem n w).conj ((successor A a).conj ((successor B A).conj ((successor C B).conj
    ((SyntaxAtomSyntax.atomic w a z n).conj (ForcingCodeRecursion.compiled R H w z f j a n Q))))))
def atomicSentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C n Q : Fin m) : Source.Sentence :=
  ((atomicInput R H w z f j a A B C n Q).imp (ForcingAtomCode.compiled R w a z n Q)).close
theorem atomic_kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C n Q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (atomicSentence R H w z f j a A B C n Q)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := atomicInput R H w z f j a A B C n Q
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact atomic (ZFContext.add (ZFContext.source_ZF m) E) R H w z f j a A B C n Q (.conjL h) (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h))) (.conjL (.conjR (.conjR (.conjR h)))) (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h)))))) (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))

end PPAC.Migration.ForcingCodeUnary
