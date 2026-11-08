import PPAC.Migration.InternalProofTemplates

/-! Original fixed K/S logical proof steps for coded forcing preservation.
Reuse the original template factory and actual original MP nodes. All formulas,
free scopes and proofs remain internal, possibly nonstandard. No new syntax,
checker, proof kernel or truth/forcing predicate. Ordinary implication proof
composition here is NOT the forcing-specific compiled-implication bridge. -/
namespace PPAC.Migration.InternalProofImplication
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open YesMetaZFC.Automation
open ObjectTreeTemplate (Template)
open InternalProofConjunction (proved proved_rename modus_ponens)
set_option maxRecDepth 16384

private theorem imp_graph {n m} {Γ : Context m} (t u : Template n) (w X Y Q : Fin m) (env : Fin n → Fin m)
    (hx : Derives Γ (graph t.expr w env X)) (hy : Derives Γ (graph u.expr w env Y))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two X Y) Q)) :
    Derives Γ (graph (Template.binary 7 t u).expr w env Q) := by
  let es : Fin 2 → ObjectHorn.Expr n := Fin.cases t.expr (fun _ => u.expr)
  change Derives Γ (graph (ObjectHorn.Expr.node (.literal 7) (List.ofFn es)) w env Q)
  exact HornExprForest.constructor_graph 2 7 es w Q env (SyntaxAtomSyntax.two X Y)
    (fun i => Fin.cases hx (fun i => Fin.cases hy (fun e => Fin.elim0 e) i) i) hc
private theorem imp_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b A B I : Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A B) I)) : Derives Γ (formulaCode w I z b) :=
  .impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z b A B I hw hc))
    (.conjI (.conjR (FormulaCodeProperties.guards w A z b hA)) (.conjI hA hB))

/-- Instantiate an ORIGINAL implication axiom, generate its actual code/proof,
and apply one actual MP. Fixed-table membership is proved externally; every
runtime formula/proof and intermediate witness is an internal object. -/
theorem apply_axiom {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (tag : Nat) (left right : Template (n+1))
    (ht : InternalProofTemplates.admissible (.binary 7 left right))
    (hactual : ObjectLogicalAxiom.prop tag n (Template.binary 7 left right).expr ∈ ObjectLogicalAxiom.shapes)
    (w z L R : Fin m) (env : Fin (n+1) → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hctx : Derives Γ (SyntaxTermSyntax.contexts w z (env 0)))
    (hn : Derives Γ (environmentNat (n+1) w env))
    (hTypes : Derives Γ (LogicalStaticQueries.types n false w z env))
    (hs : ∀ i, i ∈ (Template.binary 7 left right).expr.variables → Derives Γ (formulaCode w (env i) z (env 0)))
    (hL : Derives Γ (graph left.expr w env L)) (hR : Derives Γ (graph right.expr w env R))
    (hp : Derives Γ (proved test w z (env 0) L)) : Derives Γ (proved test w z (env 0) R) := by
  have hsl (i) (hi : i ∈ left.expr.variables) := hs i (by
    simpa only [Template.expr, ObjectHorn.Expr.node, ObjectHorn.Expr.list, ObjectHorn.Expr.variables,
      List.nil_append, List.append_nil, List.mem_append] using (Or.inl hi : i ∈ left.expr.variables ∨ i ∈ right.expr.variables))
  have hsr (i) (hi : i ∈ right.expr.variables) := hs i (by
    simpa only [Template.expr, ObjectHorn.Expr.node, ObjectHorn.Expr.list, ObjectHorn.Expr.variables,
      List.nil_append, List.append_nil, List.mem_append] using (Or.inr hi : i ∈ left.expr.variables ∨ i ∈ right.expr.variables))
  have hLT := InternalProofTemplates.template_type left ht.2.1 hZ w z (env 0) L env hw hctx hn hsl hL
  have hRT := InternalProofTemplates.template_type right ht.2.2 hZ w z (env 0) R env hw hctx hn hsr hR
  have hLN := Derives.conjL (FormulaCodeProperties.guards w L z (env 0) hLT)
  have hRN := Derives.conjL (FormulaCodeProperties.guards w R z (env 0) hRT)
  have hin := SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two L R)
    (fun i => Fin.cases hLN (fun i => Fin.cases hRN (fun e => Fin.elim0 e) i) i)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two L.castSucc R.castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have he : Derives Γ (.ex T) := of_eq (by simp only [T, SyntaxNodeSyntax.existsConstructor, SyntaxAtomSyntax.two_map])
    (SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two L R) hw hin)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ T
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz T)
  have hctx1 := of_eq (SyntaxTermSyntax.contexts_rename w z (env 0) Fin.castSucc) (under hctx T)
  have hn1 := of_eq (environmentNat_rename (n+1) w env Fin.castSucc) (under hn T)
  have hTypes1 : Derives Δ (LogicalStaticQueries.types n false w.castSucc z.castSucc (fun i => (env i).castSucc)) :=
    of_eq (by simp only [Formula.raise, LogicalStaticQueries.types, LogicalStaticQueries.conjoin_rename,
      LogicalStaticQueries.typed, Bool.false_eq_true, ↓reduceIte, formulaCode_rename]) (under hTypes T)
  have hs1 (i) (hi : i ∈ (Template.binary 7 left right).expr.variables) :=
    of_eq (formulaCode_rename w (env i) z (env 0) Fin.castSucc) (under (hs i hi) T)
  have hL1 := of_eq (graph_rename left.expr w L env Fin.castSucc) (under hL T)
  have hR1 := of_eq (graph_rename right.expr w R env Fin.castSucc) (under hR T)
  have hG := imp_graph left right w.castSucc L.castSucc R.castSucc (Fin.last m) (fun i => (env i).castSucc) hL1 hR1 (.conjR hT)
  have hAX := InternalProofTemplates.template_axiom hZ1 test tag (.binary 7 left right) ht hactual
    w.castSucc z.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hz1 hctx1 hn1 hTypes1 hs1 hG
  have out := modus_ponens hZ1 test w.castSucc z.castSucc (env 0).castSucc L.castSucc R.castSucc (Fin.last m) hw1 hz1
    (of_eq (formulaCode_rename w L z (env 0) Fin.castSucc) (under hLT T))
    (of_eq (formulaCode_rename w R z (env 0) Fin.castSucc) (under hRT T)) (.conjR hT)
    (of_eq (proved_rename test w z (env 0) L Fin.castSucc) (under hp T)) hAX
  exact of_eq (proved_rename test w z (env 0) R Fin.castSucc).symm out

private def kLeft : Template 3 := .hole 1
private def kRight : Template 3 := .binary 7 (.hole 2) (.hole 1)
private def kTemplate : Template 3 := .binary 7 kLeft kRight
private theorem k_admissible : InternalProofTemplates.admissible kTemplate := by
  simp [kTemplate, kLeft, kRight, InternalProofTemplates.admissible]
private theorem k_original : ObjectLogicalAxiom.prop 2 2 kTemplate.expr ∈ ObjectLogicalAxiom.shapes := by
  change ObjectLogicalAxiom.rule2 ∈ ObjectLogicalAxiom.shapes
  simp only [ObjectLogicalAxiom.shapes, List.mem_cons, or_true, true_or]
private theorem k_no_zero : 0 ∉ kTemplate.expr.variables := by decide

/-- Original K/rule2 plus actual MP: a real proof of B produces a real proof
of A→B. The implication code is the actual supplied constructor, not a quote. -/
theorem weaken_proof {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b A B I : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A B) I))
    (hp : Derives Γ (proved test w z b B)) : Derives Γ (proved test w z b I) := by
  let env := SetLanguage.args3 b B A
  have hgA := FormulaCodeProperties.guards w A z b hA
  have hgB := FormulaCodeProperties.guards w B z b hB
  have hn : Derives Γ (environmentNat 3 w env) :=
    .conjI (.conjR (.conjR hgB)) (.conjI (.conjL hgB) (.conjI (.conjL hgA) HornRuleSyntax.truth_proved))
  have hs : ∀ i, i ∈ kTemplate.expr.variables → Derives Γ (formulaCode w (env i) z b) := by
    intro i
    refine Fin.cases ?_ (fun i => Fin.cases (fun _ => hB) (fun i => Fin.cases (fun _ => hA) (fun e => Fin.elim0 e) i) i) i
    intro hi
    exact False.elim (k_no_zero hi)
  have hTypes : Derives Γ (LogicalStaticQueries.types 2 false w z env) := .conjI hB (.conjI hA HornRuleSyntax.truth_proved)
  have hL : Derives Γ (graph kLeft.expr w env B) := .conjI (.conjL hgB) (.eqRefl _)
  have hR := imp_graph (.hole 2 : Template 3) (.hole 1) w A B I env
    (.conjI (.conjL hgA) (.eqRefl _)) (.conjI (.conjL hgB) (.eqRefl _)) hc
  exact apply_axiom hZ test 2 kLeft kRight k_admissible k_original w z B I env hw hz (.conjR hgB) hn hTypes hs hL hR hp

private def sA : Template 4 := .hole 1
private def sB : Template 4 := .hole 2
private def sC : Template 4 := .hole 3
private def sLeft : Template 4 := .binary 7 sA (.binary 7 sB sC)
private def sRight : Template 4 := .binary 7 (.binary 7 sA sB) (.binary 7 sA sC)
private def sTemplate : Template 4 := .binary 7 sLeft sRight
private theorem s_admissible : InternalProofTemplates.admissible sTemplate := by
  simp [sTemplate, sLeft, sRight, sA, sB, sC, InternalProofTemplates.admissible]
private theorem s_original : ObjectLogicalAxiom.prop 0 3 sTemplate.expr ∈ ObjectLogicalAxiom.shapes := by
  change ObjectLogicalAxiom.rule0 ∈ ObjectLogicalAxiom.shapes
  simp only [ObjectLogicalAxiom.shapes, List.mem_cons, true_or]
private theorem s_no_zero : 0 ∉ sTemplate.expr.variables := by decide
private def four {m} (b A B C : Fin m) : Fin 4 → Fin m := Fin.cases b (Fin.cases A (SyntaxAtomSyntax.two B C))

private theorem distribute_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B C I J K L D : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b)) (hC : Derives Γ (formulaCode w C z b))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A B) I))
    (hJ : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two B C) J))
    (hK : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A C) K))
    (hL : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A J) L))
    (hD : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two I K) D))
    (hpL : Derives Γ (proved test w z b L)) (hpI : Derives Γ (proved test w z b I)) : Derives Γ (proved test w z b K) := by
  let env := four b A B C
  have hgA := FormulaCodeProperties.guards w A z b hA
  have hgB := FormulaCodeProperties.guards w B z b hB
  have hgC := FormulaCodeProperties.guards w C z b hC
  have hn : Derives Γ (environmentNat 4 w env) := .conjI (.conjR (.conjR hgA))
    (.conjI (.conjL hgA) (.conjI (.conjL hgB) (.conjI (.conjL hgC) HornRuleSyntax.truth_proved)))
  have hs : ∀ i, i ∈ sTemplate.expr.variables → Derives Γ (formulaCode w (env i) z b) := by
    intro i
    refine Fin.cases ?_ (fun i => Fin.cases (fun _ => hA) (fun i => Fin.cases (fun _ => hB)
      (fun i => Fin.cases (fun _ => hC) (fun e => Fin.elim0 e) i) i) i) i
    intro hi
    exact False.elim (s_no_zero hi)
  have hTypes : Derives Γ (LogicalStaticQueries.types 3 false w z env) := .conjI hA (.conjI hB (.conjI hC HornRuleSyntax.truth_proved))
  have gA : Derives Γ (graph sA.expr w env A) := .conjI (.conjL hgA) (.eqRefl _)
  have gB : Derives Γ (graph sB.expr w env B) := .conjI (.conjL hgB) (.eqRefl _)
  have gC : Derives Γ (graph sC.expr w env C) := .conjI (.conjL hgC) (.eqRefl _)
  have gJ := imp_graph sB sC w B C J env gB gC hJ
  have gL := imp_graph sA (.binary 7 sB sC) w A J L env gA gJ hL
  have gI := imp_graph sA sB w A B I env gA gB hI
  have gK := imp_graph sA sC w A C K env gA gC hK
  have gD := imp_graph (.binary 7 sA sB) (.binary 7 sA sC) w I K D env gI gK hD
  have hpD := apply_axiom hZ test 0 sLeft sRight s_admissible s_original w z L D env hw hz (.conjR hgA) hn hTypes hs gL gD hpL
  exact modus_ponens hZ test w z b I K D hw hz (imp_type hZ w z b A B I hw hA hB hI)
    (imp_type hZ w z b A C K hw hA hC hK) hD hpI hpD

/-- Original S/rule0 plus two actual MP nodes. No proof of the distribution
axiom or intermediate implication code is supplied. -/
theorem distribute {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B C I J K L : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b)) (hC : Derives Γ (formulaCode w C z b))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A B) I))
    (hJ : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two B C) J))
    (hK : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A C) K))
    (hL : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A J) L))
    (hpL : Derives Γ (proved test w z b L)) (hpI : Derives Γ (proved test w z b I)) : Derives Γ (proved test w z b K) := by
  have hIN := Derives.conjL (FormulaCodeProperties.guards w I z b (imp_type hZ w z b A B I hw hA hB hI))
  have hKN := Derives.conjL (FormulaCodeProperties.guards w K z b (imp_type hZ w z b A C K hw hA hC hK))
  have hin := SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two I K)
    (fun i => Fin.cases hIN (fun i => Fin.cases hKN (fun e => Fin.elim0 e) i) i)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two I.castSucc K.castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have he : Derives Γ (.ex T) := of_eq (by simp only [T, SyntaxNodeSyntax.existsConstructor, SyntaxAtomSyntax.two_map])
    (SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two I K) hw hin)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have out := distribute_at (ZFContext.under hZ T) test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc C.castSucc
    I.castSucc J.castSucc K.castSucc L.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (of_eq (empty_rename z Fin.castSucc) (under hz T))
    (of_eq (formulaCode_rename w A z b Fin.castSucc) (under hA T))
    (of_eq (formulaCode_rename w B z b Fin.castSucc) (under hB T))
    (of_eq (formulaCode_rename w C z b Fin.castSucc) (under hC T))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hI T))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hJ T))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hK T))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hL T)) (.conjR hT)
    (of_eq (proved_rename test w z b L Fin.castSucc) (under hpL T)) (of_eq (proved_rename test w z b I Fin.castSucc) (under hpI T))
  exact of_eq (proved_rename test w z b K Fin.castSucc).symm out

/-- Compose actual proofs of A→B and B→C into an actual proof of A→C.
Both original K/S instances, every intermediate code and all MP parents are
constructed internally, even for nonstandard formulas/free scopes/proofs. -/
theorem compose {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B C I J K : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b)) (hC : Derives Γ (formulaCode w C z b))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A B) I))
    (hJ : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two B C) J))
    (hK : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A C) K))
    (hpI : Derives Γ (proved test w z b I)) (hpJ : Derives Γ (proved test w z b J)) : Derives Γ (proved test w z b K) := by
  have hJT := imp_type hZ w z b B C J hw hB hC hJ
  have hAN := Derives.conjL (FormulaCodeProperties.guards w A z b hA)
  have hJN := Derives.conjL (FormulaCodeProperties.guards w J z b hJT)
  have hin := SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two A J)
    (fun i => Fin.cases hAN (fun i => Fin.cases hJN (fun e => Fin.elim0 e) i) i)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two A.castSucc J.castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have he : Derives Γ (.ex T) := of_eq (by simp only [T, SyntaxNodeSyntax.existsConstructor, SyntaxAtomSyntax.two_map])
    (SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two A J) hw hin)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ T
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz T)
  have hA1 := of_eq (formulaCode_rename w A z b Fin.castSucc) (under hA T)
  have hB1 := of_eq (formulaCode_rename w B z b Fin.castSucc) (under hB T)
  have hC1 := of_eq (formulaCode_rename w C z b Fin.castSucc) (under hC T)
  have hI1 : Derives Δ (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two A.castSucc B.castSucc) I.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hI T)
  have hJ1 : Derives Δ (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two B.castSucc C.castSucc) J.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hJ T)
  have hK1 : Derives Δ (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two A.castSucc C.castSucc) K.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hK T)
  have hpI1 := of_eq (proved_rename test w z b I Fin.castSucc) (under hpI T)
  have hpJ1 := of_eq (proved_rename test w z b J Fin.castSucc) (under hpJ T)
  have hpL := weaken_proof hZ1 test w.castSucc z.castSucc b.castSucc A.castSucc J.castSucc (Fin.last m)
    hw1 hz1 hA1 (imp_type hZ1 w.castSucc z.castSucc b.castSucc B.castSucc C.castSucc J.castSucc hw1 hB1 hC1 hJ1) (.conjR hT) hpJ1
  have out := distribute hZ1 test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc C.castSucc I.castSucc J.castSucc K.castSucc (Fin.last m)
    hw1 hz1 hA1 hB1 hC1 hI1 hJ1 hK1 (.conjR hT) hpL hpI1
  exact of_eq (proved_rename test w z b K Fin.castSucc).symm out

def input {m} (test : Formula 1) (w z b A B C I J K : Fin m) : Formula m :=
  (formulaCode w A z b).conj ((formulaCode w B z b).conj ((formulaCode w C z b).conj
    ((SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A B) I).conj
      ((SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two B C) J).conj
        ((SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two A C) K).conj
          ((proved test w z b I).conj (proved test w z b J)))))))

def sentence {m} (target : Bool) (w z b A B C I J K : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((input (OriginalAxiomCodeTest.test target) w z b A B C I J K).imp
    (proved (OriginalAxiomCodeTest.test target) w z b K)))).close

theorem kernel_certificate {m} (target : Bool) (w z b A B C I J K : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence target w z b A B C I J K)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Γ := Context.add (input (OriginalAxiomCodeTest.test target) w z b A B C I J K)
    (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have h : Derives Γ (input (OriginalAxiomCodeTest.test target) w z b A B C I J K) := .hyp (Or.inl rfl)
  exact compose (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _)
    (OriginalAxiomCodeTest.test target) w z b A B C I J K
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl)))
    (.conjL h) (.conjL (.conjR h)) (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h)))) (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))

end PPAC.Migration.InternalProofImplication
