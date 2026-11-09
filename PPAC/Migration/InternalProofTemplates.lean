import PPAC.Migration.InternalProofConjunction
import YesMetaZFC.Automation.ObjectTreeTemplate

/-! Fixed propositional proof templates reuse the ORIGINAL ObjectTreeTemplate
and original formula constructors. Holes hold arbitrary internal formula codes,
including nonstandard ones. No new object syntax, checker or proof kernel.
The consumers are the conjunction projections and fixed logical steps in the
pinned forcing monotonicity/regularity proofs, not a uniform truth predicate. -/
namespace PPAC.Migration.InternalProofTemplates
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open YesMetaZFC.Automation
open ObjectTreeTemplate (Template)
set_option maxRecDepth 16384

/-- A condition on EXTERNAL fixed templates only. Hole contents are unrestricted
internal formulas; this does not impose external standardness on them. -/
def admissible {n} : Template n → Prop
  | .hole _ => True
  | .leaf tag => tag = 0 ∨ tag = 1
  | .unary tag body => tag = 4 ∧ admissible body
  | .binary tag left right => (tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8) ∧ admissible left ∧ admissible right

private theorem unary_member {n} (tag : Nat) (t : Template n) (i : Fin n) (hi : i ∈ t.expr.variables) :
    i ∈ (Template.unary tag t).expr.variables := by
  simpa only [Template.expr, ObjectHorn.Expr.node, ObjectHorn.Expr.list, ObjectHorn.Expr.variables,
    List.nil_append, List.append_nil] using hi
private theorem binary_left_member {n} (tag : Nat) (t u : Template n) (i : Fin n) (hi : i ∈ t.expr.variables) :
    i ∈ (Template.binary tag t u).expr.variables := by
  simpa only [Template.expr, ObjectHorn.Expr.node, ObjectHorn.Expr.list, ObjectHorn.Expr.variables,
    List.nil_append, List.append_nil, List.mem_append] using (Or.inl hi : i ∈ t.expr.variables ∨ i ∈ u.expr.variables)
private theorem binary_right_member {n} (tag : Nat) (t u : Template n) (i : Fin n) (hi : i ∈ u.expr.variables) :
    i ∈ (Template.binary tag t u).expr.variables := by
  simpa only [Template.expr, ObjectHorn.Expr.node, ObjectHorn.Expr.list, ObjectHorn.Expr.variables,
    List.nil_append, List.append_nil, List.mem_append] using (Or.inr hi : i ∈ t.expr.variables ∨ i ∈ u.expr.variables)

private theorem binary_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat)
    (ht : tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8) (w z b X Y Q : Fin m)
    (hw : Derives Γ (omega w)) (hctx : Derives Γ (SyntaxTermSyntax.contexts w z b))
    (hx : Derives Γ (formulaCode w X z b)) (hy : Derives Γ (formulaCode w Y z b))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 tag w (SyntaxAtomSyntax.two X Y) Q)) : Derives Γ (formulaCode w Q z b) := by
  have hs : Derives Γ (FormulaCodeBranchSyntax.binaryTypes w z b X Y) := .conjI hctx (.conjI hx hy)
  rcases ht with rfl | rfl | rfl | rfl
  · exact .impE (.conjR (FormulaCodeKnownLogical.binary0_iff hZ w z b X Y Q hw hc)) hs
  · exact .impE (.conjR (FormulaCodeKnownLogical.binary1_iff hZ w z b X Y Q hw hc)) hs
  · exact .impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z b X Y Q hw hc)) hs
  · exact .impE (.conjR (FormulaCodeKnownLogical.binary3_iff hZ w z b X Y Q hw hc)) hs

/-- Original full FormulaCode for any actual value of a fixed template. The
proof only reads original graph witnesses and existing constructor/type laws. -/
theorem template_type {n} (t : Template n) (ht : admissible t) {m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (w z b Q : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hctx : Derives Γ (SyntaxTermSyntax.contexts w z b))
    (hn : Derives Γ (environmentNat n w env))
    (hs : ∀ i, i ∈ t.expr.variables → Derives Γ (formulaCode w (env i) z b))
    (hg : Derives Γ (graph t.expr w env Q)) : Derives Γ (formulaCode w Q z b) := by
  induction t generalizing m with
  | hole i =>
    have hi : i ∈ (Template.hole i).expr.variables := by simp only [Template.expr, ObjectHorn.Expr.variables, List.mem_singleton]
    exact FormulaCodeTransport.code_root w (env i) z b Q (eq_symm (.conjR hg)) (hs i hi)
  | leaf tag =>
    have hc := Derives.impE (.conjL (HornExprConstructor.constructor_iff hZ 0 tag (fun i => Fin.elim0 i) w Q env (fun i => Fin.elim0 i) hw hn (fun i => Fin.elim0 i))) hg
    rcases ht with rfl | rfl
    · exact .impE (.conjR (FormulaCodeKnownAtomic.nullary_iff hZ false w z b Q hw hc)) hctx
    · exact .impE (.conjR (FormulaCodeKnownAtomic.nullary_iff hZ true w z b Q hw hc)) hctx
  | unary tag t ih =>
    obtain ⟨rfl, ht⟩ := ht
    let X := (Formula.mem (Fin.last m) w.castSucc).conj (graph t.expr w.castSucc (fun i => (env i).castSucc) (Fin.last m))
    let Δ := Context.add X (Context.image Formula.raise Γ)
    apply Derives.exE (p := X) (HornExprExistence.exists_value hZ t.expr w env hw hn)
    have hx : Derives Δ X := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under hZ X
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw X)
    have hctx1 := of_eq (SyntaxTermSyntax.contexts_rename w z b Fin.castSucc) (under hctx X)
    have hn1 := of_eq (environmentNat_rename n w env Fin.castSucc) (under hn X)
    have hs1 (i) (hi : i ∈ t.expr.variables) := of_eq (formulaCode_rename w (env i) z b Fin.castSucc)
      (under (hs i (unary_member 4 t i hi)) X)
    have htX := ih ht hZ1 w.castSucc z.castSucc b.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hctx1 hn1 hs1 (.conjR hx)
    have hg1 := of_eq (graph_rename (Template.unary 4 t).expr w Q env Fin.castSucc) (under hg X)
    have hc := Derives.impE (.conjL (HornExprConstructor.constructor_iff hZ1 1 4 (fun _ : Fin 1 => t.expr)
      w.castSucc Q.castSucc (fun i => (env i).castSucc) (fun _ => Fin.last m) hw1 hn1 (fun _ => .conjR hx))) hg1
    have out := Derives.impE (.conjR (FormulaCodeKnownLogical.negation_iff hZ1 w.castSucc z.castSucc b.castSucc (Fin.last m) Q.castSucc hw1 hc)) (.conjI hctx1 htX)
    exact of_eq (formulaCode_rename w Q z b Fin.castSucc).symm out
  | binary tag t u iht ihu =>
    obtain ⟨htag, ht, hu⟩ := ht
    let X := (Formula.mem (Fin.last m) w.castSucc).conj (graph t.expr w.castSucc (fun i => (env i).castSucc) (Fin.last m))
    let Δ := Context.add X (Context.image Formula.raise Γ)
    apply Derives.exE (p := X) (HornExprExistence.exists_value hZ t.expr w env hw hn)
    have hx : Derives Δ X := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under hZ X
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw X)
    have hctx1 := of_eq (SyntaxTermSyntax.contexts_rename w z b Fin.castSucc) (under hctx X)
    have hn1 := of_eq (environmentNat_rename n w env Fin.castSucc) (under hn X)
    have hst1 (i) (hi : i ∈ t.expr.variables) := of_eq (formulaCode_rename w (env i) z b Fin.castSucc)
      (under (hs i (binary_left_member tag t u i hi)) X)
    have hXt := iht ht hZ1 w.castSucc z.castSucc b.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hctx1 hn1 hst1 (.conjR hx)
    have hg1 := of_eq (graph_rename (Template.binary tag t u).expr w Q env Fin.castSucc) (under hg X)
    let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
      (graph u.expr w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last (m+1)))
    let Ξ := Context.add Y (Context.image Formula.raise Δ)
    have outer : Derives Δ (formulaCode w.castSucc Q.castSucc z.castSucc b.castSucc) := by
      apply Derives.exE (p := Y) (HornExprExistence.exists_value hZ1 u.expr w.castSucc (fun i => (env i).castSucc) hw1 hn1)
      have hy : Derives Ξ Y := .hyp (Or.inl rfl)
      have hZ2 := ZFContext.under hZ1 Y
      have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Y)
      have hctx2 := of_eq (SyntaxTermSyntax.contexts_rename w.castSucc z.castSucc b.castSucc Fin.castSucc) (under hctx1 Y)
      have hn2 := of_eq (environmentNat_rename n w.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hn1 Y)
      have hsu2 (i) (hi : i ∈ u.expr.variables) := of_eq (formulaCode_rename w.castSucc (env i).castSucc z.castSucc b.castSucc Fin.castSucc)
        (under (of_eq (formulaCode_rename w (env i) z b Fin.castSucc) (under (hs i (binary_right_member tag t u i hi)) X)) Y)
      have hYt := ihu hu hZ2 w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))
        (fun i => (env i).castSucc.castSucc) hw2 hctx2 hn2 hsu2 (.conjR hy)
      have hXt2 := of_eq (formulaCode_rename w.castSucc (Fin.last m) z.castSucc b.castSucc Fin.castSucc) (under hXt Y)
      have hx2 := of_eq (graph_rename t.expr w.castSucc (Fin.last m) (fun i => (env i).castSucc) Fin.castSucc) (under (.conjR hx) Y)
      have hg2 := of_eq (graph_rename (Template.binary tag t u).expr w.castSucc Q.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hg1 Y)
      let exprs : Fin 2 → ObjectHorn.Expr n := Fin.cases t.expr (fun _ => u.expr)
      have hc := Derives.impE (.conjL (HornExprConstructor.constructor_iff hZ2 2 tag exprs
        w.castSucc.castSucc Q.castSucc.castSucc (fun i => (env i).castSucc.castSucc)
        (SyntaxAtomSyntax.two (Fin.last m).castSucc (Fin.last (m+1))) hw2 hn2
        (fun i => Fin.cases hx2 (fun i => Fin.cases (.conjR hy) (fun e => Fin.elim0 e) i) i))) hg2
      have out := binary_type hZ2 tag htag w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc
        (Fin.last m).castSucc (Fin.last (m+1)) Q.castSucc.castSucc hw2 hctx2 hXt2 hYt hc
      exact of_eq (formulaCode_rename w.castSucc Q.castSucc z.castSucc b.castSucc Fin.castSucc).symm out
    exact of_eq (formulaCode_rename w Q z b Fin.castSucc).symm outer

private theorem ofFn_finRange {α} (n : Nat) (f : Fin n → α) : List.ofFn f = (List.finRange n).map f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.ofFn_succ, List.finRange_succ, List.map_cons, List.map_map, ih, Function.comp_def]

private theorem types_rename {m l} (n : Nat) (w z : Fin m) (env : Fin (n+1) → Fin m) (r : Fin m → Fin l) :
    (LogicalStaticQueries.types n false w z env).rename r =
      LogicalStaticQueries.types n false (r w) (r z) (fun i => r (env i)) := by
  simp only [LogicalStaticQueries.types, LogicalStaticQueries.conjoin_rename, LogicalStaticQueries.typed, Bool.false_eq_true, ↓reduceIte, formulaCode_rename]

/-- Repackage the actual original logical proof, without changing its witness
or interpreting a logical test as a proof. -/
theorem logical_proof {m} {Γ : Context m} (test : Formula 1) (w z b F c : Fin m)
    (h : Derives Γ (InternalProofOperations.existsResult test 0 w z (SetLanguage.args3 b F c))) :
    Derives Γ (InternalProofConjunction.proved test w z b F) := by
  let T := InternalProofOperations.result test 0 w.castSucc z.castSucc (Fin.last m) (fun i => (SetLanguage.args3 b F c i).castSucc)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) h
  have ht : Derives Δ T := .hyp (Or.inl rfl)
  have out : Derives Δ (InternalProofConjunction.proved test w.castSucc z.castSucc b.castSucc F.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, InternalMPProof.annotated_rename,
      empty_rename, ProofTreeEntryFacts.root_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (show Derives Δ ((Formula.mem (Fin.last m) w.castSucc).conj
        ((InternalMPProof.annotated test w.castSucc z.castSucc b.castSucc F.castSucc (Fin.last m)).conj
          ((empty b.castSucc).imp (ProofTreeEntrySyntax.root test w.castSucc (Fin.last m) F.castSucc)))) from
        .conjI (.conjL ht) (.conjR (.conjR ht)))
  exact of_eq (InternalProofConjunction.proved_rename test w z b F Fin.castSucc).symm out

private theorem template_at_row {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (tag : Nat) (t : Template (n+1)) (ht : admissible t)
    (hactual : ObjectLogicalAxiom.prop tag n t.expr ∈ ObjectLogicalAxiom.shapes)
    (w z F c row : Fin m) (env : Fin (n+1) → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hctx : Derives Γ (SyntaxTermSyntax.contexts w z (env 0)))
    (hn : Derives Γ (environmentNat (n+1) w env))
    (hTypes : Derives Γ (LogicalStaticQueries.types n false w z env))
    (hs : ∀ i, i ∈ t.expr.variables → Derives Γ (formulaCode w (env i) z (env 0)))
    (hg : Derives Γ (graph t.expr w env F))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor n tag w (fun i => env i.succ) c))
    (hr : Derives Γ (SyntaxNodeSyntax.constructor 3 0 w (SetLanguage.args3 (env 0) c F) row)) :
    Derives Γ (InternalProofConjunction.proved test w z (env 0) F) := by
  let cexpr : ObjectHorn.Expr (n+1) := ObjectLogicalAxiom.node tag ((List.finRange n).map (fun i => .var i.succ))
  let shape := ObjectLogicalAxiom.prop tag n t.expr
  have hcG : Derives Γ (graph cexpr w env c) := by
    have h := HornExprForest.constructor_graph n tag (fun i => .var i.succ) w c env (fun i => env i.succ)
      (fun i => .conjI (environmentNat_at w env hn i.succ) (.eqRefl _)) hc
    exact of_eq (by simp only [cexpr, ofFn_finRange]) h
  let es : Fin 3 → ObjectHorn.Expr (n+1) := Fin.cases (.var 0) (Fin.cases cexpr (fun _ => t.expr))
  have hh : Derives Γ (graph shape.head w env row) :=
    HornExprForest.constructor_graph 3 0 es w row env (SetLanguage.args3 (env 0) c F)
      (fun i => Fin.cases (.conjI (environmentNat_at w env hn 0) (.eqRefl _))
        (fun i => Fin.cases hcG (fun i => Fin.cases hg (fun e => Fin.elim0 e) i) i) i) hr
  have hb := LogicalStaticNode.head_bounds hZ shape.head (ObjectLogicalAxiom.head_variables shape hactual) w row env hw hn hh
  have hqs0 := Derives.impE (.conjR (LogicalStaticQueries.bundle_iff hZ n false w z env hw hn hz)) hTypes
  have hqs : Derives Γ (LogicalStaticQueryList.listBundle shape.queries w env) :=
    of_eq (LogicalStaticQueryList.original_bundle n false w env).symm hqs0
  have hm : Derives Γ (LogicalOriginalNodeSyntax.matrix shape w row env) := .conjI hn (.conjI hb (.conjI hh hqs))
  have hnode : Derives Γ (LogicalOriginalNodeSyntax.node shape w row) := by
    apply HornBinderRules.intro_many (n+1) (LogicalOriginalNodeSyntax.body shape w row) env
    change Derives Γ ((LogicalOriginalNodeSyntax.matrix shape (old (n+1) w) (old (n+1) row) (slot (n+1))).rename (assign (n+1) env))
    exact of_eq (by simp only [LogicalTableRenaming.matrix_rename, assign_old, assign_slot]) hm
  have htable : Derives Γ (LogicalOriginalNodeSyntax.table w row) := ProofTreeRootSyntax.disjoin_intro _ _
    (List.mem_map.mpr ⟨shape, hactual, rfl⟩) hnode
  have hquery : Derives Γ (OriginalLogicalExprQuery.rowQuery 3 0 w (SetLanguage.args3 (env 0) c F)) := by
    apply Derives.exI row
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
      LogicalTableRenaming.table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr htable)
  have hF := template_type t ht hZ w z (env 0) F env hw hctx hn hs hg
  have hcN := ProofTreeConstructorFacts.range hZ n tag w c (fun i => env i.succ) hw hc
  exact logical_proof test w z (env 0) F c (InternalProofOperations.logical hZ test w z (env 0) F c hw hz (.conjI hF (.conjI hcN hquery)))

private theorem template_at_certificate {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (tag : Nat) (t : Template (n+1)) (ht : admissible t)
    (hactual : ObjectLogicalAxiom.prop tag n t.expr ∈ ObjectLogicalAxiom.shapes)
    (w z F c : Fin m) (env : Fin (n+1) → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hctx : Derives Γ (SyntaxTermSyntax.contexts w z (env 0)))
    (hn : Derives Γ (environmentNat (n+1) w env))
    (hTypes : Derives Γ (LogicalStaticQueries.types n false w z env))
    (hs : ∀ i, i ∈ t.expr.variables → Derives Γ (formulaCode w (env i) z (env 0)))
    (hg : Derives Γ (graph t.expr w env F))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor n tag w (fun i => env i.succ) c)) :
    Derives Γ (InternalProofConjunction.proved test w z (env 0) F) := by
  have hF := template_type t ht hZ w z (env 0) F env hw hctx hn hs hg
  have hcN := ProofTreeConstructorFacts.range hZ n tag w c (fun i => env i.succ) hw hc
  have hFN := Derives.conjL (FormulaCodeProperties.guards w F z (env 0) hF)
  have hin := SyntaxForestSyntax.intro_inputs 3 w (SetLanguage.args3 (env 0) c F)
    (fun i => Fin.cases (environmentNat_at w env hn 0) (fun i => Fin.cases hcN (fun i => Fin.cases hFN (fun e => Fin.elim0 e) i) i) i)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 3 0 w.castSucc (fun i => (SetLanguage.args3 (env 0) c F i).castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (SyntaxConstructors.exists_constructor hZ 3 0 w (SetLanguage.args3 (env 0) c F) hw hin)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have out := template_at_row (ZFContext.under hZ T) test tag t ht hactual w.castSucc z.castSucc F.castSucc c.castSucc (Fin.last m) (fun i => (env i).castSucc)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (of_eq (empty_rename z Fin.castSucc) (under hz T))
    (of_eq (SyntaxTermSyntax.contexts_rename w z (env 0) Fin.castSucc) (under hctx T))
    (of_eq (environmentNat_rename (n+1) w env Fin.castSucc) (under hn T))
    (of_eq (types_rename n w z env Fin.castSucc) (under hTypes T))
    (fun i hi => of_eq (formulaCode_rename w (env i) z (env 0) Fin.castSucc) (under (hs i hi) T))
    (of_eq (graph_rename t.expr w F env Fin.castSucc) (under hg T))
    (of_eq (SyntaxNodeSyntax.constructor_rename n tag w (fun i => env i.succ) c Fin.castSucc) (under hc T)) (.conjR hT)
  exact of_eq (InternalProofConjunction.proved_rename test w z (env 0) F Fin.castSucc).symm out

/-- Uniform actual proof production for a FIXED propositional axiom from the
original table. The external membership check rules out arbitrary templates;
all hole values and proof codes remain arbitrary internal objects. The original
certificate, complete grammar queries, table row and parent proof are generated. -/
theorem template_axiom {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (tag : Nat) (t : Template (n+1)) (ht : admissible t)
    (hactual : ObjectLogicalAxiom.prop tag n t.expr ∈ ObjectLogicalAxiom.shapes)
    (w z F : Fin m) (env : Fin (n+1) → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hctx : Derives Γ (SyntaxTermSyntax.contexts w z (env 0)))
    (hn : Derives Γ (environmentNat (n+1) w env))
    (hTypes : Derives Γ (LogicalStaticQueries.types n false w z env))
    (hs : ∀ i, i ∈ t.expr.variables → Derives Γ (formulaCode w (env i) z (env 0)))
    (hg : Derives Γ (graph t.expr w env F)) :
    Derives Γ (InternalProofConjunction.proved test w z (env 0) F) := by
  have hin := SyntaxForestSyntax.intro_inputs n w (fun i => env i.succ) (fun i => environmentNat_at w env hn i.succ)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor n tag w.castSucc (fun i => (env i.succ).castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (SyntaxConstructors.exists_constructor hZ n tag w (fun i => env i.succ) hw hin)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have out := template_at_certificate (ZFContext.under hZ T) test tag t ht hactual w.castSucc z.castSucc F.castSucc (Fin.last m) (fun i => (env i).castSucc)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (of_eq (empty_rename z Fin.castSucc) (under hz T))
    (of_eq (SyntaxTermSyntax.contexts_rename w z (env 0) Fin.castSucc) (under hctx T))
    (of_eq (environmentNat_rename (n+1) w env Fin.castSucc) (under hn T))
    (of_eq (types_rename n w z env Fin.castSucc) (under hTypes T))
    (fun i hi => of_eq (formulaCode_rename w (env i) z (env 0) Fin.castSucc) (under (hs i hi) T))
    (of_eq (graph_rename t.expr w F env Fin.castSucc) (under hg T)) (.conjR hT)
  exact of_eq (InternalProofConjunction.proved_rename test w z (env 0) F Fin.castSucc).symm out

private def selected {α} (right : Bool) (a b : α) : α := if right then b else a
private theorem selected_map {α β} (right : Bool) (a b : α) (f : α → β) :
    f (selected right a b) = selected right (f a) (f b) := by cases right <;> rfl
private def projectionTemplate (right : Bool) : Template 3 :=
  .binary 7 (.binary 5 (.hole 1) (.hole 2)) (.hole (selected right 1 2))
private theorem projection_admissible (right : Bool) : admissible (projectionTemplate right) := by
  cases right <;> simp [projectionTemplate, admissible]
private theorem projection_original (right : Bool) :
    ObjectLogicalAxiom.prop (selected right 12 13) 2 (projectionTemplate right).expr ∈ ObjectLogicalAxiom.shapes := by
  cases right with
  | false =>
    change ObjectLogicalAxiom.rule12 ∈ ObjectLogicalAxiom.shapes
    simp only [ObjectLogicalAxiom.shapes, List.mem_cons, or_true, true_or]
  | true =>
    change ObjectLogicalAxiom.rule13 ∈ ObjectLogicalAxiom.shapes
    simp only [ObjectLogicalAxiom.shapes, List.mem_cons, or_true, true_or]
private theorem projection_variables (right : Bool) (i : Fin 3) :
    i ∈ (projectionTemplate right).expr.variables ↔ i = 1 ∨ i = 2 := by
  cases right <;> simp [projectionTemplate, selected, Template.expr, ObjectHorn.Expr.node,
    ObjectHorn.Expr.list, ObjectHorn.Expr.variables, or_comm]

/-- The EXISTING original rule12/13 axiom proof, factored from its former
MP consumer. No truth or proof of the conjunction C is assumed. -/
theorem projection_axiom {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (right : Bool)
    (w z b A B C I : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 5 w (SyntaxAtomSyntax.two A B) C))
    (hi : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two C (selected right A B)) I)) :
    Derives Γ (InternalProofConjunction.proved test w z b I) := by
  let env := SetLanguage.args3 b A B
  have hgA := FormulaCodeProperties.guards w A z b hA
  have hgB := FormulaCodeProperties.guards w B z b hB
  have hn : Derives Γ (environmentNat 3 w env) :=
    .conjI (.conjR (.conjR hgA)) (.conjI (.conjL hgA) (.conjI (.conjL hgB) HornRuleSyntax.truth_proved))
  have hctx : Derives Γ (SyntaxTermSyntax.contexts w z b) := .conjR hgA
  have hs (i : Fin 3) (hmem : i ∈ (projectionTemplate right).expr.variables) : Derives Γ (formulaCode w (env i) z b) := by
    rcases (projection_variables right i).mp hmem with rfl | rfl
    · exact hA
    · exact hB
  have htypes : Derives Γ (LogicalStaticQueries.types 2 false w z env) := .conjI hA (.conjI hB HornRuleSyntax.truth_proved)
  let leftExpr : ObjectHorn.Expr 3 := (Template.binary 5 (.hole 1) (.hole 2)).expr
  let ce : Fin 2 → ObjectHorn.Expr 3 := Fin.cases (.var 1) (fun _ => .var 2)
  have hcG : Derives Γ (graph leftExpr w env C) := by
    change Derives Γ (graph (ObjectHorn.Expr.node (.literal 5) (List.ofFn ce)) w env C)
    exact HornExprForest.constructor_graph 2 5 ce w C env (SyntaxAtomSyntax.two A B)
      (fun i => Fin.cases (.conjI (.conjL hgA) (.eqRefl _))
        (fun i => Fin.cases (.conjI (.conjL hgB) (.eqRefl _)) (fun e => Fin.elim0 e) i) i) hc
  have htG : Derives Γ (graph (Template.hole (selected right 1 2)).expr w env (selected right A B)) := by
    cases right
    · exact .conjI (.conjL hgA) (.eqRefl _)
    · exact .conjI (.conjL hgB) (.eqRefl _)
  let ie : Fin 2 → ObjectHorn.Expr 3 := Fin.cases leftExpr (fun _ => (Template.hole (selected right 1 2)).expr)
  have hiG : Derives Γ (graph (projectionTemplate right).expr w env I) := by
    change Derives Γ (graph (ObjectHorn.Expr.node (.literal 7) (List.ofFn ie)) w env I)
    exact HornExprForest.constructor_graph 2 7 ie w I env (SyntaxAtomSyntax.two C (selected right A B))
      (fun i => Fin.cases hcG (fun i => Fin.cases htG (fun e => Fin.elim0 e) i) i) hi
  have haxiom := template_axiom hZ test (selected right 12 13) (projectionTemplate right) (projection_admissible right)
    (projection_original right) w z I env hw hz hctx hn htypes hs hiG
  exact haxiom


private theorem project_at_implication {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (right : Bool)
    (w z b A B C I : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 5 w (SyntaxAtomSyntax.two A B) C))
    (hi : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two C (selected right A B)) I))
    (hp : Derives Γ (InternalProofConjunction.proved test w z b C)) :
    Derives Γ (InternalProofConjunction.proved test w z b (selected right A B)) := by
  have ht : Derives Γ (formulaCode w (selected right A B) z b) := by cases right <;> assumption
  have hctx := Derives.conjR (FormulaCodeProperties.guards w A z b hA)
  have hCT := Derives.impE (.conjR (FormulaCodeKnownLogical.binary0_iff hZ w z b A B C hw hc)) (.conjI hctx (.conjI hA hB))
  have haxiom := projection_axiom hZ test right w z b A B C I hw hz hA hB hc hi
  exact InternalProofConjunction.modus_ponens hZ test w z b C (selected right A B) I hw hz hCT ht hi hp haxiom

/-- Actual original rule12/13 plus one actual MP, for arbitrary internal codes.
The implication, axiom certificate, complete query and parent proof are built. -/
theorem project {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (right : Bool)
    (w z b A B C : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 5 w (SyntaxAtomSyntax.two A B) C))
    (hp : Derives Γ (InternalProofConjunction.proved test w z b C)) :
    Derives Γ (InternalProofConjunction.proved test w z b (selected right A B)) := by
  have ht : Derives Γ (formulaCode w (selected right A B) z b) := by cases right <;> assumption
  have hCN := ProofTreeConstructorFacts.range hZ 2 5 w C (SyntaxAtomSyntax.two A B) hw hc
  have hTN := Derives.conjL (FormulaCodeProperties.guards w (selected right A B) z b ht)
  have hin := SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two C (selected right A B))
    (fun i => Fin.cases hCN (fun i => Fin.cases hTN (fun e => Fin.elim0 e) i) i)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two C.castSucc (selected right A.castSucc B.castSucc)) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have he : Derives Γ (.ex T) := of_eq (by simp only [T, SyntaxNodeSyntax.existsConstructor, SyntaxAtomSyntax.two_map, selected_map])
    (SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two C (selected right A B)) hw hin)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have out := project_at_implication (ZFContext.under hZ T) test right w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc C.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (of_eq (empty_rename z Fin.castSucc) (under hz T))
    (of_eq (formulaCode_rename w A z b Fin.castSucc) (under hA T)) (of_eq (formulaCode_rename w B z b Fin.castSucc) (under hB T))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hc T)) (.conjR hT)
    (of_eq (InternalProofConjunction.proved_rename test w z b C Fin.castSucc) (under hp T))
  have e := (InternalProofConjunction.proved_rename test w z b (selected right A B) Fin.castSucc).trans
    (congrArg (InternalProofConjunction.proved test w.castSucc z.castSucc b.castSucc) (selected_map right A B Fin.castSucc))
  exact of_eq e.symm out

/-- Direct backward consumer of the SAME accepted AND compiler output. -/
theorem project_compiled {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (R : Source.Formula (n+2)) (w z a b j N M Q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (ForcingLogicalCode.binary 0 R w z a b j N M Q))
    (hp : Derives Γ (InternalProofConjunction.proved test w z b Q)) :
    Derives Γ ((InternalProofConjunction.proved test w z b N).conj (InternalProofConjunction.proved test w z b M)) := by
  have hctor : Derives Γ (SyntaxNodeSyntax.constructor 2 5 w (SyntaxAtomSyntax.two N M) Q) := .conjL hc
  have htype := ForcingLogicalCode.binary_type 0 R w z a b j N M Q hc
  have hparts := Derives.impE (.conjL (FormulaCodeKnownLogical.binary0_iff hZ w z b N M Q hw hctor)) htype
  exact .conjI (project hZ test false w z b N M Q hw hz (.conjL (.conjR hparts)) (.conjR (.conjR hparts)) hctor hp)
    (project hZ test true w z b N M Q hw hz (.conjL (.conjR hparts)) (.conjR (.conjR hparts)) hctor hp)

/-- Bidirectional actual proof-code composition for the exact literal AND
output. This is not open closure transport or full forcing rule preservation. -/
theorem compiled_iff {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (R : Source.Formula (n+2)) (w z a b j N M Q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (ForcingLogicalCode.binary 0 R w z a b j N M Q)) :
    Derives Γ ((InternalProofConjunction.proved test w z b Q).iff
      ((InternalProofConjunction.proved test w z b N).conj (InternalProofConjunction.proved test w z b M))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact project_compiled (ZFContext.add hZ _) test R w z a b j N M Q (add hw _) (add hz _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    have h : Derives (Context.add ((InternalProofConjunction.proved test w z b N).conj (InternalProofConjunction.proved test w z b M)) Γ)
        ((InternalProofConjunction.proved test w z b N).conj (InternalProofConjunction.proved test w z b M)) := .hyp (Or.inl rfl)
    exact InternalProofConjunction.compiled_conjunction (ZFContext.add hZ _) test R w z a b j N M Q (add hw _) (add hz _) (add hc _) (.conjL h) (.conjR h)

def sentence {n m} (target : Bool) (R : Source.Formula (n+2)) (w z a b j N M Q : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((ForcingLogicalCode.binary 0 R w z a b j N M Q).imp
    ((InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w z b Q).iff
      ((InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w z b N).conj
        (InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w z b M)))))).close

theorem kernel_certificate {n m} (target : Bool) (R : Source.Formula (n+2)) (w z a b j N M Q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence target R w z a b j N M Q)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact compiled_iff (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _)
    (OriginalAxiomCodeTest.test target) R w z a b j N M Q
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.InternalProofTemplates
