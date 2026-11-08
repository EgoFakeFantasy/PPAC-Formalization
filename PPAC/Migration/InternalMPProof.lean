import PPAC.Migration.InternalAxiomProof
import PPAC.Migration.Internal.ProofTreeRootBackward
import PPAC.Migration.Internal.RawCodeFieldAtConstructor

/-! Actual original-kernel MP proof-code production at arbitrary internal free
scope. The unchanged six-rule checker checks both real child proofs, the exact
same free scope, both conclusion fields and the actual implication constructor.
The parent node/root traces are constructed, not supplied. This is the native
proof-code MP constructor used by interpretation; it does not yet supply the
forcing-implication preservation certificate or the final Con reduction. -/
namespace PPAC.Migration.InternalMPProof
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open YesMetaZFC.Automation
set_option maxRecDepth 16384

/-- The original Node predicate together with its actual two header fields. -/
def annotated {m} (test : Formula 1) (w z b F p : Fin m) : Formula m :=
  (ProofTreeEntrySyntax.node test w p).conj ((RawCodeFieldSyntax.field w p z b).conj (ProofSubstitutionProjectionSyntax.atOne w p F))
theorem annotated_rename {m l} (test : Formula 1) (w z b F p : Fin m) (r : Fin m → Fin l) :
    (annotated test w z b F p).rename r = annotated test (r w) (r z) (r b) (r F) (r p) := by
  simp only [annotated, Formula.rename, ProofTreeEntryFacts.node_rename, RawCodeFieldSyntax.field_rename, ProofSubstitutionProjectionSyntax.atOne_rename]

private def fields {m} (b B p q : Fin m) : Fin 4 → Fin m := Fin.cases b (Fin.cases B (SyntaxAtomSyntax.two p q))
private theorem fields_map {m l} (b B p q : Fin m) (r : Fin m → Fin l) :
    (fun i => r (fields b B p q i)) = fields (r b) (r B) (r p) (r q) := by
  funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun x => Fin.elim0 x) i) i) i) i

/-- The actual parent payload, accepted Node, recovered header, and a genuine
Root when its original free-context field is empty. -/
def built {m} (test : Formula 1) (w z b B p q r : Fin m) : Formula m :=
  (Formula.mem r w).conj ((SyntaxNodeSyntax.constructor 4 2 w (fields b B p q) r).conj
    ((annotated test w z b B r).conj ((empty b).imp (ProofTreeEntrySyntax.root test w r B))))
theorem built_rename {m l} (test : Formula 1) (w z b B p q r : Fin m) (rho : Fin m → Fin l) :
    (built test w z b B p q r).rename rho = built test (rho w) (rho z) (rho b) (rho B) (rho p) (rho q) (rho r) := by
  simp only [built, Formula.rename, SyntaxNodeSyntax.constructor_rename, fields_map, annotated_rename, empty_rename, ProofTreeEntryFacts.root_rename]

def existsBuilt {m} (test : Formula 1) (w z b B p q : Fin m) : Formula m := .ex
  (built test w.castSucc z.castSucc b.castSucc B.castSucc p.castSucc q.castSucc (Fin.last m))
theorem existsBuilt_rename {m l} (test : Formula 1) (w z b B p q : Fin m) (r : Fin m → Fin l) :
    (existsBuilt test w z b B p q).rename r = existsBuilt test (r w) (r z) (r b) (r B) (r p) (r q) := by
  simp only [existsBuilt, Formula.rename, built_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem node_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w p : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (ProofTreeEntrySyntax.node test w p)) : Derives Γ (.mem p w) := by
  let T := (SyntaxNodeSyntax.constructor 1 0 w.castSucc (fun _ => p.castSucc) (Fin.last m)).conj
    (ProofTreeTraceSyntax.condition test w.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) hp
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hr := ProofTreeConstructorFacts.range (ZFContext.under hZ T) 1 0 w.castSucc (Fin.last m) (fun _ => p.castSucc) hw1 (.conjL hT)
  exact StructuralListTraceOrder.member_member (ZFContext.under hZ T) w.castSucc p.castSucc (Fin.last m) hw1 hr
    (SyntaxConstructors.child_member (ZFContext.under hZ T) 1 0 w.castSucc (fun _ => p.castSucc) (Fin.last m) 0 hw1 (.conjL hT))

private structure Inputs {m} (Γ : Context m) (test : Formula 1) (w z b A B I p q : Fin m) : Prop where
  hw : Derives Γ (omega w)
  hz : Derives Γ (empty z)
  hA : Derives Γ (formulaCode w A z b)
  hB : Derives Γ (formulaCode w B z b)
  hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A B) I)
  hp : Derives Γ (annotated test w z b A p)
  hq : Derives Γ (annotated test w z b I q)
private theorem underInputs {m} {Γ : Context m} {test : Formula 1} {w z b A B I p q : Fin m}
    (h : Inputs Γ test w z b A B I p q) (T : Formula (m+1)) :
    Inputs (Context.add T (Context.image Formula.raise Γ)) test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc I.castSucc p.castSucc q.castSucc := by
  exact ⟨of_eq (omega_rename w Fin.castSucc) (under h.hw T), of_eq (empty_rename z Fin.castSucc) (under h.hz T),
    of_eq (formulaCode_rename w A z b Fin.castSucc) (under h.hA T), of_eq (formulaCode_rename w B z b Fin.castSucc) (under h.hB T),
    of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under h.hI T),
    of_eq (annotated_rename test w z b A p Fin.castSucc) (under h.hp T), of_eq (annotated_rename test w z b I q Fin.castSucc) (under h.hq T)⟩

private theorem constructor_at_one {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B p q r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (SyntaxNodeSyntax.constructor 4 2 w (fields b B p q) r)) :
    Derives Γ (ProofSubstitutionProjectionSyntax.atOne w r B) := by
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 1 (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (SyntaxNumerals.exists_numeral hZ 1 w hw)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hr1 : Derives Δ (SyntaxNodeSyntax.constructor 4 2 w.castSucc (fields b.castSucc B.castSucc p.castSucc q.castSucc) r.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, fields_map]) (under hr T)
  have hf := RawCodeFieldAtConstructor.constructor_at (ZFContext.under hZ T) 4 2 w.castSucc (fields b.castSucc B.castSucc p.castSucc q.castSucc) r.castSucc 1 (Fin.last m) B.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) hr1 (.conjR hT)
  have ho := ProofSubstitutionProjectionSyntax.intro_atOne w.castSucc r.castSucc B.castSucc (Fin.last m) (.conjR hT) (.impE (.conjR hf) (.eqRefl _))
  exact of_eq (ProofSubstitutionProjectionSyntax.atOne_rename w r B Fin.castSucc).symm ho

private theorem from_payload {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b A B I p q r : Fin m)
    (h : Inputs Γ test w z b A B I p q) (hr : Derives Γ (SyntaxNodeSyntax.constructor 4 2 w (fields b B p q) r)) :
    Derives Γ (built test w z b B p q r) := by
  have hb := Derives.conjR (.conjR (FormulaCodeProperties.guards w B z b h.hB))
  have hBN := Derives.conjL (FormulaCodeProperties.guards w B z b h.hB)
  have hAN := Derives.conjL (FormulaCodeProperties.guards w A z b h.hA)
  have hpN := node_natural hZ test w p h.hw (.conjL h.hp)
  have hqN := node_natural hZ test w q h.hw (.conjL h.hq)
  let env : Fin 5 → Fin m := Fin.lastCases A (fields b B p q)
  have hn : Derives Γ (environmentNat 5 w env) := .conjI hb (.conjI hBN (.conjI hpN (.conjI hqN (.conjI hAN HornRuleSyntax.truth_proved))))
  have hn4 : Derives Γ (environmentNat 4 w (fields b B p q)) := .conjI hb (.conjI hBN (.conjI hpN (.conjI hqN HornRuleSyntax.truth_proved)))
  let exprs : Fin 4 → ObjectHorn.Expr 5 := fun i => .var i.castSucc
  have hs (i : Fin 4) : Derives Γ (graph (exprs i) w env (fields b B p q i)) := by
    exact of_eq (by simp only [env, exprs, graph, Fin.lastCases_castSucc]) (.conjI (environmentNat_at w env hn i.castSucc) (.eqRefl (fields b B p q i)))
  have hh : Derives Γ (graph ObjectProofNode.mpShape.head w env r) := by
    change Derives Γ (graph (.node (.literal 2) (List.ofFn exprs)) w env r)
    exact HornExprForest.constructor_graph 4 2 exprs w r env (fields b B p q) hs hr
  have himp := ProofMPSyntax.intro_implicationRead w q A B I h.hI (.conjR (.conjR h.hq))
  have hm : Derives Γ (ProofMPNodeSyntax.specificationMatrix w z r env) :=
    .conjI hn (.conjI hh (.conjI (.conjI h.hB h.hA)
      (.conjI (.conjL (.conjR h.hp)) (.conjI (.conjR (.conjR h.hp)) (.conjI (.conjL (.conjR h.hq)) himp)))))
  have hspec : Derives Γ (ProofMPNodeSyntax.specification w z r) := by
    apply HornBinderRules.intro_many 5 (ProofMPNodeSyntax.specificationBody w z r) env
    exact of_eq (by simp only [ProofMPNodeSyntax.specificationBody, ProofMPNodeSyntax.specificationMatrix_rename, assign_old, assign_slot]) hm
  have ht : Derives Γ (ProofAllNodeSyntax.table test w r) :=
    .impE (.conjR (ProofAllNodes.table_iff test hZ w z r h.hw h.hz)) (.disjR (.disjR (.disjL hspec)))
  have hmatrix : Derives Γ (ProofTreeNodeSyntax.matrix test 2 w r (fields b B p q)) :=
    .conjI hn4 (.conjI hr (.conjI (.conjL h.hp) (.conjI (.conjL h.hq) HornRuleSyntax.truth_proved)))
  have hnode := ProofTreeNodeBackward.matrix_backward test hZ 2 w r (fields b B p q) h.hw ht hmatrix
  have hfield := Derives.impE (.conjR (RawCodeFieldAtConstructor.constructor_at hZ 4 2 w (fields b B p q) r 0 z b h.hw hr h.hz)) (.eqRefl b)
  have ha : Derives Γ (annotated test w z b B r) := .conjI hnode (.conjI hfield (constructor_at_one hZ w b B p q r h.hw hr))
  have hclosed : Derives Γ ((empty b).imp (ProofTreeEntrySyntax.root test w r B)) := by
    apply Derives.impI
    exact ProofTreeRootBackward.matrix_backward test (ZFContext.add hZ _) 2 w r B (fields b B p q) (add h.hw _) (add hnode _)
      (.conjI (add hn4 _) (.conjI (add hr _) (.conjI (.hyp (Or.inl rfl)) (.eqRefl B))))
  exact .conjI (ProofTreeConstructorFacts.range hZ 4 2 w r (fields b B p q) h.hw hr) (.conjI hr (.conjI ha hclosed))

/-- Uniform original MP proof production. The two premise codes and free scope
may be nonstandard; both children and all original local tests are consumed. -/
theorem produce {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b A B I p q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A B) I))
    (hp : Derives Γ (annotated test w z b A p)) (hq : Derives Γ (annotated test w z b I q)) :
    Derives Γ (existsBuilt test w z b B p q) := by
  have hb := Derives.conjR (.conjR (FormulaCodeProperties.guards w B z b hB))
  have hBN := Derives.conjL (FormulaCodeProperties.guards w B z b hB)
  have hpN := node_natural hZ test w p hw (.conjL hp)
  have hqN := node_natural hZ test w q hw (.conjL hq)
  have hi := SyntaxForestSyntax.intro_inputs 4 w (fields b B p q) (fun i =>
    Fin.cases hb (Fin.cases hBN (Fin.cases hpN (Fin.cases hqN (fun j => Fin.elim0 j)))) i)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 4 2 w.castSucc (fields b.castSucc B.castSucc p.castSucc q.castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have hex : Derives Γ (.ex T) := of_eq (by simp only [T, SyntaxNodeSyntax.existsConstructor, fields_map]) (SyntaxConstructors.exists_constructor hZ 4 2 w (fields b B p q) hw hi)
  apply Derives.exE (p := T) hex
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hm := from_payload (ZFContext.under hZ T) test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc I.castSucc p.castSucc q.castSucc (Fin.last m)
    (underInputs ⟨hw,hz,hA,hB,hI,hp,hq⟩ T) (.conjR hT)
  have ho : Derives Δ (existsBuilt test w.castSucc z.castSucc b.castSucc B.castSucc p.castSucc q.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, built_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hm
  exact of_eq (existsBuilt_rename test w z b B p q Fin.castSucc).symm ho

/-- The actual MP payload is uniquely determined by the same two proofs,
conclusion and free scope; no canonical valid execution is assumed. -/
theorem parent_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b B p q r s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (built test w z b B p q r)) (hs : Derives Γ (built test w z b B p q s)) :
    Derives Γ (.equal r s) :=
  SyntaxConstructors.unique hZ 4 2 w (fields b B p q) r s hw (.conjL (.conjR hr)) (.conjL (.conjR hs))

def sentence {m} (target : Bool) (w z b A B I p q : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((formulaCode w A z b).imp ((formulaCode w B z b).imp
    ((SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A B) I).imp
      ((annotated (OriginalAxiomCodeTest.test target) w z b A p).imp
        ((annotated (OriginalAxiomCodeTest.test target) w z b I q).imp
          (existsBuilt (OriginalAxiomCodeTest.test target) w z b B p q)))))))).close

theorem kernel_certificate {m} (target : Bool) (w z b A B I p q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence target w z b A B I p q)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact produce (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) _) _)
    (OriginalAxiomCodeTest.test target) w z b A B I p q
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

def uniqueSentence {m} (target : Bool) (w z b B p q r s : Fin m) : Source.Sentence :=
  ((omega w).imp ((built (OriginalAxiomCodeTest.test target) w z b B p q r).imp
    ((built (OriginalAxiomCodeTest.test target) w z b B p q s).imp (.equal r s)))).close

theorem unique_kernel_certificate {m} (target : Bool) (w z b B p q r s : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (uniqueSentence target w z b B p q r s)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact parent_unique (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _)
    (OriginalAxiomCodeTest.test target) w z b B p q r s
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
end PPAC.Migration.InternalMPProof
