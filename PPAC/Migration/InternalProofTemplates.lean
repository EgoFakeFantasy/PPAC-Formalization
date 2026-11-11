import PPAC.Migration.InternalProofConjunction
import PPAC.Migration.ProjectCompilerQuotation
import PPAC.Migration.Internal.NativeTopQuotationValue
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
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)
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

private theorem quotation_graph {n} (t : Template n) (trees : Fin n → Tree)
    {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w F : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w))
    (hs : ∀ i, i ∈ t.expr.variables → Derives Γ (OriginalTreeQuotationSyntax.tree (trees i) w (env i)))
    (hq : Derives Γ (OriginalTreeQuotationSyntax.tree (t.plug trees) w F)) :
    Derives Γ (graph t.expr w env F) := by
  induction t generalizing m with
  | hole i =>
    have h := hs i (by simp [Template.expr, ObjectHorn.Expr.variables])
    exact .conjI (OriginalTreeQuotationProperties.tree_range hZ _ w (env i) hw h)
      (OriginalTreeQuotationUnique.tree_unique hZ _ w F (env i) hw hq h)
  | leaf tag =>
    have hc := OriginalQuotationNodeFields.tree_to_constructor hZ tag [] w F Fin.elim0 hw (.eqRefl w) hq
    exact HornExprForest.constructor_graph 0 tag Fin.elim0 w F env Fin.elim0 (fun i => Fin.elim0 i) hc
  | unary tag t ih =>
    let whole := Template.unary tag t
    apply ProjectCompilerQuotation.eliminate_quotations hZ 1 (fun _ => t.plug trees) w hw (graph whole.expr w env F)
    intro l Δ r xs hZ1 lift hx
    have hw1 := of_eq (omega_rename w r) (lift hw)
    have hq1 := of_eq (OriginalTreeQuotationSyntax.tree_rename (whole.plug trees) w F r) (lift hq)
    have ht := ih hZ1 (r w) (xs 0) (fun i => r (env i)) hw1
      (fun i hi => of_eq (OriginalTreeQuotationSyntax.tree_rename (trees i) w (env i) r)
        (lift (hs i (unary_member tag t i hi)))) (hx 0)
    have hc := OriginalQuotationNodeFields.tree_to_constructor hZ1 tag [t.plug trees]
      (r w) (r F) (fun _ => xs 0) hw1 (.conjI (hx 0) (.eqRefl _)) hq1
    exact of_eq (graph_rename whole.expr w F env r).symm
      (HornExprForest.constructor_graph 1 tag (fun _ => t.expr) (r w) (r F)
        (fun i => r (env i)) (fun _ => xs 0) (fun _ => ht) hc)
  | binary tag t u iht ihu =>
    let whole := Template.binary tag t u
    let children : Fin 2 → Tree := Fin.cases (t.plug trees) (fun _ => u.plug trees)
    apply ProjectCompilerQuotation.eliminate_quotations hZ 2 children w hw (graph whole.expr w env F)
    intro l Δ r xs hZ1 lift hx
    have hw1 := of_eq (omega_rename w r) (lift hw)
    have hq1 := of_eq (OriginalTreeQuotationSyntax.tree_rename (whole.plug trees) w F r) (lift hq)
    have ht := iht hZ1 (r w) (xs 0) (fun i => r (env i)) hw1
      (fun i hi => of_eq (OriginalTreeQuotationSyntax.tree_rename (trees i) w (env i) r)
        (lift (hs i (binary_left_member tag t u i hi)))) (hx 0)
    have hu := ihu hZ1 (r w) (xs 1) (fun i => r (env i)) hw1
      (fun i hi => of_eq (OriginalTreeQuotationSyntax.tree_rename (trees i) w (env i) r)
        (lift (hs i (binary_right_member tag t u i hi)))) (hx 1)
    let exprs : Fin 2 → ObjectHorn.Expr n := Fin.cases t.expr (fun _ => u.expr)
    let args := SyntaxAtomSyntax.two (xs 0) (xs 1)
    have hc := OriginalQuotationNodeFields.tree_to_constructor hZ1 tag [t.plug trees,u.plug trees]
      (r w) (r F) args hw1 (.conjI (hx 0) (.conjI (hx 1) (.eqRefl _))) hq1
    exact of_eq (graph_rename whole.expr w F env r).symm
      (HornExprForest.constructor_graph 2 tag exprs (r w) (r F) (fun i => r (env i)) args
        (fun i => Fin.cases ht (fun j => Fin.cases hu (fun k => Fin.elim0 k) j) i) hc)

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

private def originalShape {a n} (tag : Nat) (scope : Fin a) (args : Fin n → Fin a)
    (output : ObjectHorn.Expr a) (queries : List (Bool × ObjectHorn.Expr a)) : ObjectLogicalAxiom.Shape :=
  ⟨a, ObjectLogicalAxiom.head tag (.var scope) (List.ofFn (fun i => .var (args i))) output, queries⟩

private theorem logical_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (shape : ObjectLogicalAxiom.Shape) (hactual : shape ∈ ObjectLogicalAxiom.shapes)
    (w z b F c row : Fin m) (env : Fin shape.arity → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hn : Derives Γ (environmentNat shape.arity w env))
    (hh : Derives Γ (graph shape.head w env row))
    (hqs : Derives Γ (LogicalStaticQueryList.listBundle shape.queries w env))
    (hF : Derives Γ (formulaCode w F z b)) (hcN : Derives Γ (.mem c w))
    (hr : Derives Γ (SyntaxNodeSyntax.constructor 3 0 w (SetLanguage.args3 b c F) row)) :
    Derives Γ (InternalProofConjunction.proved test w z b F) := by
  have hb := HornExprBounds.intro_environmentBound row env (fun i =>
    HornExprBounds.variable_bound hZ shape.head i (ObjectLogicalAxiom.head_variables shape hactual i) w row env hw hn hh)
  have hm : Derives Γ (LogicalOriginalNodeSyntax.matrix shape w row env) := .conjI hn (.conjI hb (.conjI hh hqs))
  have hnode : Derives Γ (LogicalOriginalNodeSyntax.node shape w row) := by
    apply HornBinderRules.intro_many shape.arity (LogicalOriginalNodeSyntax.body shape w row) env
    change Derives Γ ((LogicalOriginalNodeSyntax.matrix shape (old shape.arity w) (old shape.arity row)
      (slot shape.arity)).rename (assign shape.arity env))
    exact of_eq (by simp only [LogicalTableRenaming.matrix_rename, assign_old, assign_slot]) hm
  have htable : Derives Γ (LogicalOriginalNodeSyntax.table w row) := ProofTreeRootSyntax.disjoin_intro _ _
    (List.mem_map.mpr ⟨shape, hactual, rfl⟩) hnode
  have hquery : Derives Γ (OriginalLogicalExprQuery.rowQuery 3 0 w (SetLanguage.args3 b c F)) := by
    apply Derives.exI row
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
      LogicalTableRenaming.table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr htable)
  exact logical_proof test w z b F c
    (InternalProofOperations.logical hZ test w z b F c hw hz (.conjI hF (.conjI hcN hquery)))

private theorem logical_with_certificate {a n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (tag : Nat) (scope : Fin a) (args : Fin n → Fin a) (output : ObjectHorn.Expr a)
    (queries : List (Bool × ObjectHorn.Expr a))
    (hactual : originalShape tag scope args output queries ∈ ObjectLogicalAxiom.shapes)
    (w z F c : Fin m) (env : Fin a → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hn : Derives Γ (environmentNat a w env))
    (hg : Derives Γ (graph output w env F))
    (hqs : Derives Γ (LogicalStaticQueryList.listBundle queries w env))
    (hF : Derives Γ (formulaCode w F z (env scope))) (hcN : Derives Γ (.mem c w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor n tag w (fun i => env (args i)) c)) :
    Derives Γ (InternalProofConjunction.proved test w z (env scope) F) := by
  let cert := ObjectLogicalAxiom.node tag (List.ofFn (fun i => .var (args i)))
  have hcG : Derives Γ (graph cert w env c) :=
    HornExprForest.constructor_graph n tag (fun i => .var (args i)) w c env (fun i => env (args i))
      (fun i => .conjI (environmentNat_at w env hn (args i)) (.eqRefl _)) hc
  have hb := environmentNat_at w env hn scope
  have hFN := Derives.conjL (FormulaCodeProperties.guards w F z (env scope) hF)
  let xs := SetLanguage.args3 (env scope) c F
  have hin := SyntaxForestSyntax.intro_inputs 3 w xs
    (fun i => Fin.cases hb (fun j => Fin.cases hcN (fun k => Fin.cases hFN (fun u => Fin.elim0 u) k) j) i)
  let R := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 3 0 w.castSucc (fun i => (xs i).castSucc) (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxConstructors.exists_constructor hZ 3 0 w xs hw hin)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  let env1 := fun i => (env i).castSucc
  let es : Fin 3 → ObjectHorn.Expr a := Fin.cases (.var scope) (Fin.cases cert (fun _ => output))
  have hv : Derives Δ (graph (.var scope) w.castSucc env1 (env scope).castSucc) :=
    .conjI (under hb R) (.eqRefl _)
  have hc1 := of_eq (graph_rename cert w c env Fin.castSucc) (under hcG R)
  have hg1 := of_eq (graph_rename output w F env Fin.castSucc) (under hg R)
  have hrow : Derives Δ (graph (originalShape tag scope args output queries).head w.castSucc env1 (Fin.last m)) :=
    HornExprForest.constructor_graph 3 0 es w.castSucc (Fin.last m) env1 (fun i => (xs i).castSucc)
      (fun i => Fin.cases hv (fun j => Fin.cases hc1 (fun k => Fin.cases hg1 (fun u => Fin.elim0 u) k) j) i) (.conjR hR)
  have hRow : Derives Δ (SyntaxNodeSyntax.constructor 3 0 w.castSucc
      (SetLanguage.args3 (env scope).castSucc c.castSucc F.castSucc) (Fin.last m)) := .conjR hR
  have out := logical_at_row (ZFContext.under hZ R) test _ hactual w.castSucc z.castSucc
    (env scope).castSucc F.castSucc c.castSucc (Fin.last m) env1
    (of_eq (omega_rename w Fin.castSucc) (under hw R)) (of_eq (empty_rename z Fin.castSucc) (under hz R))
    (of_eq (environmentNat_rename a w env Fin.castSucc) (under hn R)) hrow
    (of_eq (LogicalTableRenaming.listBundle_rename queries w env Fin.castSucc) (under hqs R))
    (of_eq (formulaCode_rename w F z (env scope) Fin.castSucc) (under hF R)) (under hcN R) hRow
  exact of_eq (InternalProofConjunction.proved_rename test w z (env scope) F Fin.castSucc).symm out

private theorem logical_shape {a n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (tag : Nat) (scope : Fin a) (args : Fin n → Fin a) (output : ObjectHorn.Expr a)
    (queries : List (Bool × ObjectHorn.Expr a))
    (hactual : originalShape tag scope args output queries ∈ ObjectLogicalAxiom.shapes)
    (w z F : Fin m) (env : Fin a → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hn : Derives Γ (environmentNat a w env))
    (hg : Derives Γ (graph output w env F))
    (hqs : Derives Γ (LogicalStaticQueryList.listBundle queries w env))
    (hF : Derives Γ (formulaCode w F z (env scope))) :
    Derives Γ (InternalProofConjunction.proved test w z (env scope) F) := by
  let xs := fun i => env (args i)
  have hin := SyntaxForestSyntax.intro_inputs n w xs (fun i => environmentNat_at w env hn (args i))
  let C := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor n tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m))
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply Derives.exE (p := C) (SyntaxConstructors.exists_constructor hZ n tag w xs hw hin)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have out := logical_with_certificate (ZFContext.under hZ C) test tag scope args output queries hactual
    w.castSucc z.castSucc F.castSucc (Fin.last m) (fun i => (env i).castSucc)
    (of_eq (omega_rename w Fin.castSucc) (under hw C)) (of_eq (empty_rename z Fin.castSucc) (under hz C))
    (of_eq (environmentNat_rename a w env Fin.castSucc) (under hn C))
    (of_eq (graph_rename output w F env Fin.castSucc) (under hg C))
    (of_eq (LogicalTableRenaming.listBundle_rename queries w env Fin.castSucc) (under hqs C))
    (of_eq (formulaCode_rename w F z (env scope) Fin.castSucc) (under hF C)) (.conjL hC) (.conjR hC)
  exact of_eq (InternalProofConjunction.proved_rename test w z (env scope) F Fin.castSucc).symm out

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
  let shape := ObjectLogicalAxiom.prop tag n t.expr
  have hsOriginal : originalShape tag (0 : Fin (n+1)) Fin.succ t.expr shape.queries = shape := by
    simp only [originalShape, shape, ofFn_finRange]
  have hqs := Derives.impE (.conjR (LogicalStaticQueries.bundle_iff hZ n false w z env hw hn hz)) hTypes
  exact logical_shape hZ test tag 0 Fin.succ t.expr shape.queries (hsOriginal.symm ▸ hactual) w z F env hw hz hn hg
    (of_eq (LogicalStaticQueryList.original_bundle n false w env).symm hqs)
    (template_type t ht hZ w z (env 0) F env hw hctx hn hs hg)

private theorem conjoin_intro {m} {Γ : Context m} (n : Nat) (ps : Fin n → Formula m)
    (hs : ∀ i, Derives Γ (ps i)) : Derives Γ (LogicalStaticQueries.conjoin n ps) := by
  induction n with
  | zero => exact HornRuleSyntax.truth_proved
  | succ n ih => exact .conjI (hs 0) (ih (fun i => ps i.succ) (fun i => hs i.succ))

private theorem environment_intro {m} {Γ : Context m} (n : Nat) (w : Fin m) (env : Fin n → Fin m)
    (hs : ∀ i, Derives Γ (.mem (env i) w)) : Derives Γ (environmentNat n w env) := by
  induction n with
  | zero => exact HornRuleSyntax.truth_proved
  | succ n ih => exact .conjI (hs 0) (ih (fun i => env i.succ) (fun i => hs i.succ))

private def quotationInputs {n} (trees : Fin n → Tree) : Fin (n+1) → Tree :=
  Fin.cases (.node 0 []) trees

private theorem quoted_shape {n k m} {Γ : Context m} {free : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (test : Formula 1) (tag : Nat)
    (args : Fin k → Fin (n+1)) (trees : Fin n → Tree) (t : Template (n+1))
    (queries : List (Bool × ObjectHorn.Expr (n+1)))
    (hactual : originalShape tag 0 args t.expr queries ∈ ObjectLogicalAxiom.shapes)
    (hvars : 0 ∉ t.expr.variables)
    (φ : PureSyntaxQuotation.Fm [] free)
    (hplug : PureSyntaxQuotation.formulaTree φ = t.plug (quotationInputs trees))
    (queryBundle : ∀ {l} {Δ : Context l}, ZFContext.Evidence Δ → ∀ (w z b : Fin l) (fields : Fin n → Fin l),
      Derives Δ (omega w) → Derives Δ (empty z) → Derives Δ (SyntaxNumeralSyntax.numeral free.length b) →
      (∀ i, Derives Δ (OriginalTreeQuotationSyntax.tree (trees i) w (fields i))) →
      Derives Δ (environmentNat (n+1) w (Fin.cases b fields)) →
      Derives Δ (LogicalStaticQueryList.listBundle queries w (Fin.cases b fields)))
    (w z b F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (hF : Derives Γ (PureQuotationSyntax.formula φ w F)) :
    Derives Γ (InternalProofConjunction.proved test w z b F) := by
  apply ProjectCompilerQuotation.eliminate_quotations hZ n trees w hw (InternalProofConjunction.proved test w z b F)
  intro l Δ r fields hZ1 lift hqs
  let env : Fin (n+1) → Fin l := Fin.cases (r b) fields
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  have hb1 := of_eq (SyntaxNumeralSyntax.numeral_rename free.length b r) (lift hb)
  have range (i : Fin n) := OriginalTreeQuotationProperties.tree_range hZ1 _ (r w) (fields i) hw1 (hqs i)
  have hn := environment_intro (n+1) (r w) env (fun i =>
    Fin.cases (SyntaxNumerals.range hZ1 free.length (r w) (r b) hw1 hb1) (fun j => range j) i)
  have hq (i) (hi : i ∈ t.expr.variables) :
      Derives Δ (OriginalTreeQuotationSyntax.tree (quotationInputs trees i) (r w) (env i)) := by
    refine Fin.cases ?_ (fun j _ => hqs j) i hi
    exact fun h => (hvars h).elim
  have hF1 := of_eq (PureQuotationSyntax.formula_rename φ w F r) (lift hF)
  have hg := quotation_graph t (quotationInputs trees) hZ1 (r w) (r F) env hw1 hq
    (of_eq (congrArg (fun q => OriginalTreeQuotationSyntax.tree q (r w) (r F)) hplug) hF1)
  exact of_eq (InternalProofConjunction.proved_rename test w z b F r).symm
    (logical_shape hZ1 test tag 0 args t.expr queries hactual (r w) (r z) (r F) env hw1 hz1 hn hg
      (queryBundle hZ1 (r w) (r z) (r b) fields hw1 hz1 hb1 hqs hn)
      (PureQuotationFormulaTyping.formula_type hZ1 φ (r w) (r z) (r b) (r F) hw1 hz1 hb1 hF1))

private theorem quoted_propositional {n m} {Γ : Context m} {free : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (test : Formula 1) (tag : Fin ObjectLogicalAxiom.shapes.length)
    (forms : Fin n → PureSyntaxQuotation.Fm [] free) (t : Template (n+1))
    (horiginal : ObjectLogicalAxiom.shapes.get tag = ObjectLogicalAxiom.prop tag.val n t.expr)
    (hvars : 0 ∉ t.expr.variables) {φ : PureSyntaxQuotation.Fm [] free}
    (hplug : PureSyntaxQuotation.formulaTree φ = t.plug (quotationInputs (fun i => PureSyntaxQuotation.formulaTree (forms i))))
    (w z b F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (hq : Derives Γ (PureQuotationSyntax.formula φ w F)) :
    Derives Γ (InternalProofConjunction.proved test w z b F) := by
  let shape := ObjectLogicalAxiom.prop tag.val n t.expr
  have hsOriginal : originalShape tag.val (0 : Fin (n+1)) Fin.succ t.expr shape.queries = shape := by
    simp only [originalShape, shape, ofFn_finRange]
  have ha : shape ∈ ObjectLogicalAxiom.shapes := by
    change ObjectLogicalAxiom.prop tag.val n t.expr ∈ ObjectLogicalAxiom.shapes
    rw [← horiginal]
    exact List.get_mem ObjectLogicalAxiom.shapes tag
  apply quoted_shape hZ test tag.val Fin.succ (fun i => PureSyntaxQuotation.formulaTree (forms i)) t shape.queries
    (hsOriginal.symm ▸ ha) hvars φ hplug _ w z b F hw hz hb hq
  intro l Δ hZ1 w z b fields hw1 hz1 hb1 hqs hn
  have types : Derives Δ (LogicalStaticQueries.types n false w z (Fin.cases b fields)) :=
    conjoin_intro n _ (fun i => PureQuotationFormulaTyping.formula_type hZ1 (forms i) w z b (fields i) hw1 hz1 hb1 (hqs i))
  exact of_eq (LogicalStaticQueryList.original_bundle n false w (Fin.cases b fields)).symm
    (.impE (.conjR (LogicalStaticQueries.bundle_iff hZ1 n false w z _ hw1 hn hz1)) types)

open YesMetaZFC.Logic.FirstOrder (HilbertBaseAxiom)
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature

private abbrev implicationTemplate {n} := @Template.binary n 7
private abbrev conjunctionTemplate {n} := @Template.binary n 5
private abbrev disjunctionTemplate {n} := @Template.binary n 6
private abbrev biconditionalTemplate {n} := @Template.binary n 8
private abbrev negationTemplate {n} := @Template.unary n 4

theorem eliminate_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n : Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (x : Fin l),
      ZFContext.Evidence Δ → (∀ {p : Formula m}, Derives Γ p → Derives Δ (p.rename r)) →
      Derives Δ (successor x (r n)) → Derives Δ (out.rename r)) :
    Derives Γ out := by
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) n.castSucc)
  apply Derives.exE (p := B) (.impE (OmegaSyntax.step_at w n (.conjL hw)) hn)
  exact use Fin.castSucc (Fin.last m) (ZFContext.under hZ B) (fun hp => under hp B) (.conjR (.hyp (Or.inl rfl)))

open YesMetaZFC.SetTheory (SetSort)

private def instantiationAxiom {free : PureSyntaxQuotation.Ctx}
    (universal : Bool) (body : PureSyntaxQuotation.Fm [.set] free)
    (term : PureSyntaxQuotation.Tm [] free SetSort.set) : PureSyntaxQuotation.Fm [] free :=
  if universal then .imp (.forallE .set body) (body.instantiateTop term)
  else .imp (body.instantiateTop term) (.existsE .set body)

private theorem instantiation_queries {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z A : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hn : Derives Γ (environmentNat 4 w env))
    (hA : Derives Γ (successor A z))
    (hF : Derives Γ (formulaCode w (env 1) A (env 0)))
    (ht : Derives Γ (SyntaxTermSyntax.term w z (env 0) (env 2)))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z (env 0) A (env 2) (env 1) (env 3))) :
    Derives Γ (LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule20.queries w env) := by
  have spec := LogicalInstantiateSyntax.intro_specification4 w z A env hA (.conjI hF (.conjI ht hi))
  have bundle := Derives.impE (.conjR (LogicalInstantiateAllQueries.bundle4_iff hZ w z env hw hn hz)) spec
  exact .impE (.conjR (LogicalOriginalQueryBundles.original_bundle20_iff w env)) bundle

open LogicalRule23Head in
/-- Original rule 23 for an actual instance at an arbitrary internal term. -/
theorem existential_introduction_axiom {m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b A F t N E I : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z b A t F N))
    (he : Derives Γ (SyntaxLogicalSyntax.singleCode 10 w F E))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w N E I)) :
    Derives Γ (InternalProofConjunction.proved test w z b I) := by
  let env : Fin 4 → Fin m := Fin.cases b (SetLanguage.args3 F t N)
  have hEnv := SyntaxTopFormulaTyping.instantiate_environment w z b A t F N hi
  have hA := Derives.conjR hEnv
  have ht := Derives.conjL hEnv
  have hF := SyntaxTopFormulaTyping.instantiate_source_type hZ w z b A t F N hw hi
  have hN := SyntaxTopFormulaTyping.instantiate_target_type w z b A t F N hi
  have hCtx := Derives.conjR (FormulaCodeProperties.guards w N z b hN)
  have hE := Derives.impE (.conjR (FormulaCodeKnownLogical.quantified_iff hZ false w z b F E A hw he hA))
    (.conjI hCtx hF)
  have hI := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z b N E I hw hc))
    (.conjI hCtx (.conjI hN hE))
  have hn : Derives Γ (environmentNat 4 w env) :=
    .conjI (.conjR hCtx) (.conjI (.conjL (FormulaCodeProperties.guards w F A b hF))
      (.conjI (SyntaxTerms.range hZ w z b t hw ht)
        (.conjI (.conjL (FormulaCodeProperties.guards w N z b hN)) HornRuleSyntax.truth_proved)))
  have hField : (fun _ : Fin 1 => F) = fields1 env := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have h1 := Derives.impE (.conjR (node1_iff hZ w E env hw hn))
    (of_eq (congrArg (fun xs => SyntaxNodeSyntax.constructor 1 10 w xs E) hField) he)
  have h2 := Derives.impE (.conjR (node2_iff hZ w I E env hw hn h1)) hc
  have hqs := instantiation_queries hZ w z A env hw hz hn hA hF ht hi
  exact logical_shape hZ test 23 0 (fun i : Fin 2 => ([1,2][i] : Fin 4)) part2
    ObjectLogicalAxiom.rule20.queries (by
      change ObjectLogicalAxiom.rule23 ∈ ObjectLogicalAxiom.shapes
      simp only [ObjectLogicalAxiom.shapes, List.mem_cons, true_or, or_true])
    w z I env hw hz hn h2 hqs hI

private theorem instantiate_quotation {m} {Γ : Context m} {free : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (test : Formula 1) (universal : Bool)
    (body : PureSyntaxQuotation.Fm [.set] free) (term : PureSyntaxQuotation.Tm [] free SetSort.set)
    (w z b F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (hq : Derives Γ (PureQuotationSyntax.formula (instantiationAxiom universal body term) w F)) :
    Derives Γ (InternalProofConjunction.proved test w z b F) := by
  let t : Template 4 :=
    if universal then implicationTemplate (.unary 9 (.hole 1)) (.hole 3)
    else implicationTemplate (.hole 3) (.unary 10 (.hole 1))
  let trees := fun i : Fin 3 =>
    [PureSyntaxQuotation.formulaTree body, PureSyntaxQuotation.termTree term,
      PureSyntaxQuotation.formulaTree (body.instantiateTop term)][i]
  let tag := if universal then 20 else 23
  let args := fun i : Fin 2 => ([1,2][i] : Fin 4)
  have hactual : originalShape tag 0 args t.expr ObjectLogicalAxiom.rule20.queries ∈ ObjectLogicalAxiom.shapes := by
    cases universal
    · change ObjectLogicalAxiom.rule23 ∈ ObjectLogicalAxiom.shapes
      simp only [ObjectLogicalAxiom.shapes, List.mem_cons, true_or, or_true]
    · change ObjectLogicalAxiom.rule20 ∈ ObjectLogicalAxiom.shapes
      simp only [ObjectLogicalAxiom.shapes, List.mem_cons, true_or, or_true]
  apply quoted_shape hZ test tag args trees t ObjectLogicalAxiom.rule20.queries hactual
    (by cases universal <;> decide) (instantiationAxiom universal body term) (by cases universal <;> rfl)
    _ w z b F hw hz hb hq
  intro l Δ hZ1 w z b fields hw1 hz1 hb1 hqs hn
  let env : Fin 4 → Fin l := Fin.cases b fields
  let out := LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule20.queries w env
  apply eliminate_successor hZ1 w z hw1 (SyntaxNumerals.range hZ1 0 w z hw1 hz1) out
  intro l' Δ' r A hZ2 lift hA
  let env2 := fun i => r (env i)
  have hw2 := of_eq (omega_rename w r) (lift hw1)
  have hz2 := of_eq (empty_rename z r) (lift hz1)
  have hb2 := of_eq (SyntaxNumeralSyntax.numeral_rename free.length b r) (lift hb1)
  have hn2 := of_eq (environmentNat_rename 4 w env r) (lift hn)
  have hs (i : Fin 3) := of_eq (OriginalTreeQuotationSyntax.tree_rename (trees i) w (fields i) r) (lift (hqs i))
  have ha := SyntaxNumeralSyntax.intro_succ 0 A (r z) hz2 hA
  have hBody := PureQuotationFormulaTyping.formula_type hZ2 body (r w) A (r b) (r (fields 0)) hw2 ha hb2 (hs 0)
  have hTerm := PureQuotationTermTyping.term_type hZ2 term (r w) (r z) (r b) (r (fields 1)) hw2 hz2 hb2 (hs 1)
  have hInst := NativeTopQuotationValue.instantiate_at_candidate hZ2 body term
    (r w) (r z) (r b) A (r (fields 1)) (r (fields 0)) (r (fields 2)) hw2 hz2 hb2 (hs 1) (hs 0) hA (hs 2)
  exact of_eq (LogicalTableRenaming.listBundle_rename ObjectLogicalAxiom.rule20.queries w env r).symm
    (instantiation_queries hZ2 (r w) (r z) A env2 hw2 hz2 hn2 hA hBody hTerm (.conjL hInst))

private theorem reflexivity_quotation {m} {Γ : Context m} {free : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (test : Formula 1) (term : PureSyntaxQuotation.Tm [] free SetSort.set)
    (w z b F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (hq : Derives Γ (PureQuotationSyntax.formula (.equal term term) w F)) :
    Derives Γ (InternalProofConjunction.proved test w z b F) := by
  let t : Template 2 := .binary 3 (.hole 1) (.hole 1)
  apply quoted_shape hZ test 26 (fun _ : Fin 1 => (1 : Fin 2)) (fun _ => PureSyntaxQuotation.termTree term)
    t ObjectLogicalAxiom.rule26.queries (by
      change ObjectLogicalAxiom.rule26 ∈ ObjectLogicalAxiom.shapes
      simp only [ObjectLogicalAxiom.shapes, List.mem_cons, true_or, or_true])
    (by decide) (.equal term term) rfl _ w z b F hw hz hb hq
  intro l Δ hZ1 w z b fields hw1 hz1 hb1 hqs hn
  let env : Fin 2 → Fin l := Fin.cases b fields
  have ht := PureQuotationTermTyping.term_type hZ1 term w z b (fields 0) hw1 hz1 hb1 (hqs 0)
  have types : Derives Δ (LogicalStaticQueries.types 1 true w z env) := .conjI ht HornRuleSyntax.truth_proved
  exact of_eq (LogicalStaticQueryList.original_bundle 1 true w env).symm
    (.impE (.conjR (LogicalStaticQueries.bundle_iff hZ1 1 true w z env hw1 hn hz1)) types)

private theorem equality_substitution_quotation {m} {Γ : Context m} {free : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (left right : PureSyntaxQuotation.Tm [] free SetSort.set) (body : PureSyntaxQuotation.Fm [.set] free)
    (w z b F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (hq : Derives Γ (PureQuotationSyntax.formula
      (.imp (.equal left right) (.imp (body.instantiateTop left) (body.instantiateTop right))) w F)) :
    Derives Γ (InternalProofConjunction.proved test w z b F) := by
  let t : Template 6 := implicationTemplate (.binary 3 (.hole 1) (.hole 2)) (implicationTemplate (.hole 4) (.hole 5))
  let trees := fun i : Fin 5 => [PureSyntaxQuotation.termTree left, PureSyntaxQuotation.termTree right,
    PureSyntaxQuotation.formulaTree body, PureSyntaxQuotation.formulaTree (body.instantiateTop left),
    PureSyntaxQuotation.formulaTree (body.instantiateTop right)][i]
  let args := fun i : Fin 3 => ([1,2,3][i] : Fin 6)
  apply quoted_shape hZ test 25 args trees t ObjectLogicalAxiom.rule25.queries (by
    change ObjectLogicalAxiom.rule25 ∈ ObjectLogicalAxiom.shapes
    simp only [ObjectLogicalAxiom.shapes, List.mem_cons, true_or, or_true])
    (by decide) _ rfl _ w z b F hw hz hb hq
  intro l Δ hZ1 w z b fields hw1 hz1 hb1 hqs hn
  let env : Fin 6 → Fin l := Fin.cases b fields
  let out := LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule25.queries w env
  apply eliminate_successor hZ1 w z hw1 (SyntaxNumerals.range hZ1 0 w z hw1 hz1) out
  intro l' Δ' r A hZ2 lift hA
  let env2 := fun i => r (env i)
  have hw2 := of_eq (omega_rename w r) (lift hw1)
  have hz2 := of_eq (empty_rename z r) (lift hz1)
  have hb2 := of_eq (SyntaxNumeralSyntax.numeral_rename free.length b r) (lift hb1)
  have hn2 := of_eq (environmentNat_rename 6 w env r) (lift hn)
  have hs (i : Fin 5) := of_eq (OriginalTreeQuotationSyntax.tree_rename (trees i) w (fields i) r) (lift (hqs i))
  have ha := SyntaxNumeralSyntax.intro_succ 0 A (r z) hz2 hA
  have hBody := PureQuotationFormulaTyping.formula_type hZ2 body (r w) A (r b) (r (fields 2)) hw2 ha hb2 (hs 2)
  have hLeft := PureQuotationTermTyping.term_type hZ2 left (r w) (r z) (r b) (r (fields 0)) hw2 hz2 hb2 (hs 0)
  have hRight := PureQuotationTermTyping.term_type hZ2 right (r w) (r z) (r b) (r (fields 1)) hw2 hz2 hb2 (hs 1)
  have hInstL := NativeTopQuotationValue.instantiate_at_candidate hZ2 body left
    (r w) (r z) (r b) A (r (fields 0)) (r (fields 2)) (r (fields 3)) hw2 hz2 hb2 (hs 0) (hs 2) hA (hs 3)
  have hInstR := NativeTopQuotationValue.instantiate_at_candidate hZ2 body right
    (r w) (r z) (r b) A (r (fields 1)) (r (fields 2)) (r (fields 4)) hw2 hz2 hb2 (hs 1) (hs 2) hA (hs 4)
  have spec := LogicalInstantiateSyntax.intro_specification6 (r w) (r z) A env2 hA
    (.conjI hLeft (.conjI hRight (.conjI hBody (.conjI (.conjL hInstL) (.conjL hInstR)))))
  have bundle := Derives.impE (.conjR (LogicalInstantiateAllQueries.bundle6_iff hZ2 (r w) (r z) env2 hw2 hn2 hz2)) spec
  exact of_eq (LogicalTableRenaming.listBundle_rename ObjectLogicalAxiom.rule25.queries w env r).symm
    (.impE (.conjR (LogicalOriginalQueryBundles.original_bundle25_iff (r w) env2)) bundle)

open YesMetaZFC.Logic.FirstOrder (VariableRenaming VariableSubstitution)

theorem quotation_rename_indices {sb sf tb tf : PureSyntaxQuotation.Ctx}
    (br : VariableRenaming sb tb) (fr : VariableRenaming sf tf)
    (hb : ∀ {sort} (v : YesMetaZFC.Logic.FirstOrder.Variable sb sort), (br v).index = v.index)
    (hf : ∀ {sort} (v : YesMetaZFC.Logic.FirstOrder.Variable sf sort), (fr v).index = v.index)
    (φ : PureSyntaxQuotation.Fm sb sf) :
    PureSyntaxQuotation.formulaTree (φ.renameMapped br fr) = PureSyntaxQuotation.formulaTree φ := by
  open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT in
  have a := PureSyntaxOperations.formula_substitute SyntaxSubstitution.bvar SyntaxSubstitution.fvar
    (fun v => .bvar (br v)) (fun v => .fvar (fr v))
    (fun v => congrArg SyntaxSubstitution.bvar (hb v).symm)
    (fun v => congrArg SyntaxSubstitution.fvar (hf v).symm) φ
  open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT in
  have b := PureSyntaxOperations.formula_substitute SyntaxSubstitution.bvar SyntaxSubstitution.fvar
    VariableSubstitution.boundId VariableSubstitution.freeId (fun _ => rfl) (fun _ => rfl) φ
  rw [← YesMetaZFC.Logic.FirstOrder.Formula.renameMapped_eq_substituteMapped] at a
  rw [YesMetaZFC.Logic.FirstOrder.Formula.substituteMapped_id] at b
  exact a.symm.trans b

private theorem vacuous_body {free : PureSyntaxQuotation.Ctx} (body : PureSyntaxQuotation.Fm [] free) :
    PureSyntaxQuotation.formulaTree ((body.weakenFree SetSort.set).abstractFreeTop) =
      PureSyntaxQuotation.formulaTree body := by
  open YesMetaZFC.Logic.FirstOrder in
  change PureSyntaxQuotation.formulaTree ((body.weakenFree SetSort.set).substituteMapped
    (VariableSubstitution.abstractBound (σ := ℒ) (bound := []) (free := free) SetSort.set)
    (VariableSubstitution.abstractFreeTop (σ := ℒ) (bound := []))) = _
  rw [YesMetaZFC.Logic.FirstOrder.Formula.substituteMapped_weakenFree_tail]
  change PureSyntaxQuotation.formulaTree (body.substituteMapped
    (VariableSubstitution.of_bound_renaming (VariableRenaming.weaken SetSort.set))
    VariableSubstitution.freeId) = _
  rw [YesMetaZFC.Logic.FirstOrder.Formula.substituteMapped_of_bound_renaming]
  exact quotation_rename_indices _ _ (by intro sort v; cases v) (fun _ => rfl) body

private theorem vacuous_quotation {m} {Γ : Context m} {free : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (test : Formula 1) (body : PureSyntaxQuotation.Fm [] free)
    (w z b F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (hq : Derives Γ (PureQuotationSyntax.formula (.imp body ((body.weakenFree SetSort.set).forallFreeTop SetSort.set)) w F)) :
    Derives Γ (InternalProofConjunction.proved test w z b F) := by
  let t : Template 2 := implicationTemplate (.hole 1) (.unary 9 (.hole 1))
  apply quoted_shape hZ test 22 (fun _ : Fin 1 => (1 : Fin 2)) (fun _ => PureSyntaxQuotation.formulaTree body)
    t ObjectLogicalAxiom.rule22.queries (by
      change ObjectLogicalAxiom.rule22 ∈ ObjectLogicalAxiom.shapes
      simp only [ObjectLogicalAxiom.shapes, List.mem_cons, true_or, or_true])
    (by decide) _ ?_ _ w z b F hw hz hb hq
  · change Tree.node 7 [PureSyntaxQuotation.formulaTree body,
        .node 9 [PureSyntaxQuotation.formulaTree ((body.weakenFree SetSort.set).abstractFreeTop)]] = _
    rw [vacuous_body]
    rfl
  · intro l Δ hZ1 w z b fields hw1 hz1 hb1 hqs hn
    let env : Fin 2 → Fin l := Fin.cases b fields
    have hBody := PureQuotationFormulaTyping.formula_type hZ1 body w z b (fields 0) hw1 hz1 hb1 (hqs 0)
    have types : Derives Δ (LogicalStaticQueries.types 1 false w z env) := .conjI hBody HornRuleSyntax.truth_proved
    exact of_eq (LogicalStaticQueryList.original_bundle 1 false w env).symm
      (.impE (.conjR (LogicalStaticQueries.bundle_iff hZ1 1 false w z env hw1 hn hz1)) types)

theorem eliminate_binder_scopes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (.mem z w))
    (hb : Derives Γ (.mem b w)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (A B : Fin l),
      ZFContext.Evidence Δ → (∀ {p : Formula m}, Derives Γ p → Derives Δ (p.rename r)) →
      Derives Δ (successor A (r z)) → Derives Δ (successor B (r b)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  apply eliminate_successor hZ w z hw hz out
  intro l Δ r A hZ1 lift hA
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hb1 : Derives Δ (.mem (r b) (r w)) := lift hb
  apply eliminate_successor hZ1 (r w) (r b) hw1 hb1 (out.rename r)
  intro l' Δ' s B hZ2 move hB
  let rs := fun i => s (r i)
  have lift2 {p : Formula m} (hp : Derives Γ p) : Derives Δ' (p.rename rs) :=
    of_eq (rename_comp p r s) (move (lift hp))
  exact of_eq (rename_comp out r s).symm
    (use rs (s A) B hZ2 lift2 (of_eq (successor_rename A (r z) s) (move hA)) hB)

private theorem forall_distribution_quotation {m} {Γ : Context m} {free : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (test : Formula 1) (left right : PureSyntaxQuotation.Fm [] (.set :: free))
    (w z b F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (hq : Derives Γ (PureQuotationSyntax.formula
      (.imp ((left.imp right).forallFreeTop .set) (.imp (left.forallFreeTop .set) (right.forallFreeTop .set))) w F)) :
    Derives Γ (InternalProofConjunction.proved test w z b F) := by
  let t : Template 5 := implicationTemplate (.unary 9 (implicationTemplate (.hole 3) (.hole 4)))
    (implicationTemplate (.unary 9 (.hole 3)) (.unary 9 (.hole 4)))
  let trees := fun i : Fin 4 => [PureSyntaxQuotation.formulaTree left, PureSyntaxQuotation.formulaTree right,
    PureSyntaxQuotation.formulaTree left.abstractFreeTop, PureSyntaxQuotation.formulaTree right.abstractFreeTop][i]
  let args := fun i : Fin 2 => ([1,2][i] : Fin 5)
  apply quoted_shape hZ test 21 args trees t ObjectLogicalAxiom.rule21.queries (by
    change ObjectLogicalAxiom.rule21 ∈ ObjectLogicalAxiom.shapes
    simp only [ObjectLogicalAxiom.shapes, List.mem_cons, true_or, or_true])
    (by decide) _ rfl _ w z b F hw hz hb hq
  intro l Δ hZ1 w z b fields hw1 hz1 hb1 hqs hn
  let env : Fin 5 → Fin l := Fin.cases b fields
  let out := LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule21.queries w env
  apply eliminate_binder_scopes hZ1 w z b hw1 (SyntaxNumerals.range hZ1 0 w z hw1 hz1)
    (SyntaxNumerals.range hZ1 free.length w b hw1 hb1) out
  intro l' Δ' r A B hZ2 lift hA hB
  let env2 := fun i => r (env i)
  have hw2 := of_eq (omega_rename w r) (lift hw1)
  have hz2 := of_eq (empty_rename z r) (lift hz1)
  have hb2 := of_eq (SyntaxNumeralSyntax.numeral_rename free.length b r) (lift hb1)
  have hn2 := of_eq (environmentNat_rename 5 w env r) (lift hn)
  have hs (i : Fin 4) := of_eq (OriginalTreeQuotationSyntax.tree_rename (trees i) w (fields i) r) (lift (hqs i))
  have absLeft := Derives.conjL (NativeTopQuotationValue.abstract_at_candidate hZ2 left
    (r w) (r z) (r b) A B (r (fields 0)) (r (fields 2)) hw2 hz2 hb2 (hs 0) hA hB (hs 2))
  have absRight := Derives.conjL (NativeTopQuotationValue.abstract_at_candidate hZ2 right
    (r w) (r z) (r b) A B (r (fields 1)) (r (fields 3)) hw2 hz2 hb2 (hs 1) hA hB (hs 3))
  have hLeft := SyntaxTopFormulaTyping.abstract_source_type hZ2 (r w) (r z) (r b) A B (r (fields 0)) (r (fields 2)) hw2 absLeft
  have hRight := SyntaxTopFormulaTyping.abstract_source_type hZ2 (r w) (r z) (r b) A B (r (fields 1)) (r (fields 3)) hw2 absRight
  have step := LogicalAbstractSyntax.intro_atOneSpecification21 (r w) (r z) A B env2 hB
    (.conjI hLeft (.conjI hRight (.conjI absLeft absRight)))
  have spec := LogicalAbstractSyntax.intro_specification21 (r w) (r z) A env2 hA step
  have bundle := Derives.impE (.conjR (LogicalAbstractAllQueries.bundle21_iff hZ2 (r w) (r z) env2 hw2 hn2 hz2)) spec
  exact of_eq (LogicalTableRenaming.listBundle_rename ObjectLogicalAxiom.rule21.queries w env r).symm
    (.impE (.conjR (LogicalAbstractQueryList.original_bundle21_iff (r w) env2)) bundle)

private theorem exists_elimination_queries {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z A B : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hn : Derives Γ (environmentNat 4 w env))
    (hA : Derives Γ (successor A z)) (hB : Derives Γ (successor B (env 0)))
    (hBody : Derives Γ (formulaCode w (env 1) z B))
    (hConclusion : Derives Γ (formulaCode w (env 2) z (env 0)))
    (hAbs : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z (env 0) A B (env 1) (env 3))) :
    Derives Γ (LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule24.queries w env) := by
  have step := LogicalAbstractSyntax.intro_atOneSpecification24 w z A B env hB
    (.conjI hBody (.conjI hConclusion hAbs))
  have spec := LogicalAbstractSyntax.intro_specification24 w z A env hA step
  have bundle := Derives.impE (.conjR (LogicalAbstractAllQueries.bundle24_iff hZ w z env hw hn hz)) spec
  exact .impE (.conjR (LogicalAbstractQueryList.original_bundle24_iff w env)) bundle

open LogicalRule24Head in
set_option maxHeartbeats 1200000 in
/-- Original rule 24 for an actual internally coded body and its mode 3 abstraction. -/
theorem exists_elimination_axiom {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B Open Bound Q Branch All Ex Consequent Ax : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ha : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B Open Bound))
    (hQ : Derives Γ (formulaCode w Q z b))
    (hQBound : Derives Γ (formulaCode w Q A b))
    (hcBranch : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w Bound Q Branch))
    (hcAll : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w Branch All))
    (hcEx : Derives Γ (SyntaxLogicalSyntax.singleCode 10 w Bound Ex))
    (hcConsequent : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w Ex Q Consequent))
    (hcAx : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w All Consequent Ax)) :
    Derives Γ (InternalProofConjunction.proved test w z b Ax) := by
  let env : Fin 4 → Fin m := Fin.cases b (SetLanguage.args3 Open Q Bound)
  have hBody := SyntaxTopFormulaTyping.abstract_source_type hZ w z b A B Open Bound hw ha
  have hBound := SyntaxTopFormulaTyping.abstract_target_type w z b A B Open Bound ha
  have hEnv := SyntaxTopFormulaTyping.abstract_environment w z b A B Open Bound ha
  have hA := Derives.conjL (.conjR hEnv)
  have hB := Derives.conjR (.conjR hEnv)
  have hCtx := Derives.conjL hEnv
  have hCtxBound := Derives.conjR (FormulaCodeProperties.guards w Bound A b hBound)
  have hBranch := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w A b Bound Q Branch hw hcBranch))
    (.conjI hCtxBound (.conjI hBound hQBound))
  have hAll := Derives.impE (.conjR (FormulaCodeKnownLogical.quantified_iff hZ true w z b Branch All A hw hcAll hA))
    (.conjI hCtx hBranch)
  have hEx := Derives.impE (.conjR (FormulaCodeKnownLogical.quantified_iff hZ false w z b Bound Ex A hw hcEx hA))
    (.conjI hCtx hBound)
  have hConsequent := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z b Ex Q Consequent hw hcConsequent))
    (.conjI hCtx (.conjI hEx hQ))
  have hAx := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z b All Consequent Ax hw hcAx))
    (.conjI hCtx (.conjI hAll hConsequent))
  have hn : Derives Γ (environmentNat 4 w env) := by
    refine .conjI (.conjR (.conjR (FormulaCodeProperties.guards w Q z b hQ))) ?_
    exact .conjI (.conjL (FormulaCodeProperties.guards w Open z B hBody))
      (.conjI (.conjL (FormulaCodeProperties.guards w Q z b hQ))
        (.conjI (.conjL (FormulaCodeProperties.guards w Bound A b hBound)) HornRuleSyntax.truth_proved))
  have h1 := Derives.impE (.conjR (node1_iff hZ w Branch env hw hn)) hcBranch
  have hAllField : (fun _ : Fin 1 => Branch) = fields2 env Branch := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have hExField : (fun _ : Fin 1 => Bound) = fields3 env := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have h2 := Derives.impE (.conjR (node2_iff hZ w All Branch env hw hn h1)) (of_eq (congrArg (fun xs => SyntaxNodeSyntax.constructor 1 9 w xs All) hAllField) hcAll)
  have h3 := Derives.impE (.conjR (node3_iff hZ w Ex env hw hn)) (of_eq (congrArg (fun xs => SyntaxNodeSyntax.constructor 1 10 w xs Ex) hExField) hcEx)
  have h4 := Derives.impE (.conjR (node4_iff hZ w Consequent Ex env hw hn h3)) hcConsequent
  have h5 := Derives.impE (.conjR (node5_iff hZ w Ax All Consequent env hw hn h2 h4)) hcAx
  have hqs := exists_elimination_queries hZ w z A B env hw hz hn hA hB hBody hQ ha
  exact logical_shape hZ test 24 0 (fun i : Fin 2 => ([1,2][i] : Fin 4)) part5
    ObjectLogicalAxiom.rule24.queries (by
      change ObjectLogicalAxiom.rule24 ∈ ObjectLogicalAxiom.shapes
      simp only [ObjectLogicalAxiom.shapes, List.mem_cons, true_or, or_true])
    w z Ax env hw hz hn h5 hqs hAx

private theorem exists_elimination_quotation {m} {Γ : Context m} {free : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (test : Formula 1) (body : PureSyntaxQuotation.Fm [] (.set :: free))
    (conclusion : PureSyntaxQuotation.Fm [] free)
    (w z b F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (hq : Derives Γ (PureQuotationSyntax.formula
      (.imp ((body.imp (conclusion.weakenFree SetSort.set)).forallFreeTop .set)
        (.imp (body.existsFreeTop .set) conclusion)) w F)) :
    Derives Γ (InternalProofConjunction.proved test w z b F) := by
  let t : Template 4 := implicationTemplate (.unary 9 (implicationTemplate (.hole 3) (.hole 2)))
    (implicationTemplate (.unary 10 (.hole 3)) (.hole 2))
  let trees := fun i : Fin 3 => [PureSyntaxQuotation.formulaTree body, PureSyntaxQuotation.formulaTree conclusion,
    PureSyntaxQuotation.formulaTree body.abstractFreeTop][i]
  let args := fun i : Fin 2 => ([1,2][i] : Fin 4)
  apply quoted_shape hZ test 24 args trees t ObjectLogicalAxiom.rule24.queries (by
    change ObjectLogicalAxiom.rule24 ∈ ObjectLogicalAxiom.shapes
    simp only [ObjectLogicalAxiom.shapes, List.mem_cons, true_or, or_true])
    (by decide) _ ?_ _ w z b F hw hz hb hq
  · let abstractBody := PureSyntaxQuotation.formulaTree body.abstractFreeTop
    let antecedent := fun tree => Tree.node 9 (List.singleton (Tree.node 7 (abstractBody :: tree :: [])))
    let consequent := Tree.node 7 ((Tree.node 10 (List.singleton abstractBody)) ::
      PureSyntaxQuotation.formulaTree conclusion :: [])
    exact congrArg (fun tree => Tree.node 7 (antecedent tree :: consequent :: [])) (vacuous_body conclusion)
  · intro l Δ hZ1 w z b fields hw1 hz1 hb1 hqs hn
    let env : Fin 4 → Fin l := Fin.cases b fields
    let out := LogicalStaticQueryList.listBundle ObjectLogicalAxiom.rule24.queries w env
    apply eliminate_binder_scopes hZ1 w z b hw1 (SyntaxNumerals.range hZ1 0 w z hw1 hz1)
      (SyntaxNumerals.range hZ1 free.length w b hw1 hb1) out
    intro l' Δ' r A B hZ2 lift hA hB
    let env2 := fun i => r (env i)
    have hw2 := of_eq (omega_rename w r) (lift hw1)
    have hz2 := of_eq (empty_rename z r) (lift hz1)
    have hb2 := of_eq (SyntaxNumeralSyntax.numeral_rename free.length b r) (lift hb1)
    have hn2 := of_eq (environmentNat_rename 4 w env r) (lift hn)
    have hs (i : Fin 3) := of_eq (OriginalTreeQuotationSyntax.tree_rename (trees i) w (fields i) r) (lift (hqs i))
    have absBody := Derives.conjL (NativeTopQuotationValue.abstract_at_candidate hZ2 body
      (r w) (r z) (r b) A B (r (fields 0)) (r (fields 2)) hw2 hz2 hb2 (hs 0) hA hB (hs 2))
    have hBody := SyntaxTopFormulaTyping.abstract_source_type hZ2 (r w) (r z) (r b) A B (r (fields 0)) (r (fields 2)) hw2 absBody
    have hConclusion := PureQuotationFormulaTyping.formula_type hZ2 conclusion
      (r w) (r z) (r b) (r (fields 1)) hw2 hz2 hb2 (hs 1)
    exact of_eq (LogicalTableRenaming.listBundle_rename ObjectLogicalAxiom.rule24.queries w env r).symm
      (exists_elimination_queries hZ2 (r w) (r z) A B env2 hw2 hz2 hn2 hA hB hBody hConclusion absBody)

/-- Every original Hilbert logical axiom produces its actual proof node from
its pure-language quotation. The seven binder/equality cases use the original
grammar, instantiation and abstraction queries in the same logical table. -/
theorem from_logical_quotation {m} {Γ : Context m} {free : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (test : Formula 1) {φ : PureSyntaxQuotation.Fm [] free}
    (cert : HilbertBaseAxiom YesMetaZFC.SetTheory.signature φ)
    (w z b F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (hq : Derives Γ (PureQuotationSyntax.formula φ w F)) :
    Derives Γ (InternalProofConjunction.proved test w z b F) := by
  cases cert with
  | implication_distribution a c d =>
    refine quoted_propositional hZ test ⟨0, by decide⟩ (fun i : Fin 3 => [a,c,d][i])
      (implicationTemplate (implicationTemplate (.hole 1) (implicationTemplate (.hole 2) (.hole 3)))
        (implicationTemplate (implicationTemplate (.hole 1) (.hole 2)) (implicationTemplate (.hole 1) (.hole 3))))
      rfl (by decide) rfl w z b F hw hz hb hq
  | self_implication a =>
    refine quoted_propositional hZ test ⟨1, by decide⟩ (fun _ : Fin 1 => a)
      (implicationTemplate (.hole 1) (implicationTemplate (.hole 1) (.hole 1))) rfl (by decide) rfl w z b F hw hz hb hq
  | weakening a c =>
    refine quoted_propositional hZ test ⟨2, by decide⟩ (fun i : Fin 2 => [a,c][i])
      (implicationTemplate (.hole 1) (implicationTemplate (.hole 2) (.hole 1))) rfl (by decide) rfl w z b F hw hz hb hq
  | contradiction a c =>
    refine quoted_propositional hZ test ⟨3, by decide⟩ (fun i : Fin 2 => [a,c][i])
      (implicationTemplate (.hole 1) (implicationTemplate (negationTemplate (.hole 1)) (.hole 2))) rfl (by decide) rfl w z b F hw hz hb hq
  | classical a =>
    refine quoted_propositional hZ test ⟨4, by decide⟩ (fun _ : Fin 1 => a)
      (implicationTemplate (implicationTemplate (negationTemplate (.hole 1)) (.hole 1)) (.hole 1)) rfl (by decide) rfl w z b F hw hz hb hq
  | explosion a c =>
    refine quoted_propositional hZ test ⟨5, by decide⟩ (fun i : Fin 2 => [a,c][i])
      (implicationTemplate (negationTemplate (.hole 1)) (implicationTemplate (.hole 1) (.hole 2))) rfl (by decide) rfl w z b F hw hz hb hq
  | case_analysis a c =>
    refine quoted_propositional hZ test ⟨6, by decide⟩ (fun i : Fin 2 => [a,c][i])
      (implicationTemplate (implicationTemplate (.hole 1) (.hole 2))
        (implicationTemplate (implicationTemplate (negationTemplate (.hole 1)) (.hole 2)) (.hole 2)))
      rfl (by decide) rfl w z b F hw hz hb hq
  | truth_intro =>
    refine quoted_propositional hZ test ⟨7, by decide⟩ (fun i : Fin 0 => Fin.elim0 i) (.leaf 1) rfl (by decide) rfl w z b F hw hz hb hq
  | falsum_elimination a =>
    refine quoted_propositional hZ test ⟨8, by decide⟩ (fun _ : Fin 1 => a)
      (implicationTemplate (.leaf 0) (.hole 1)) rfl (by decide) rfl w z b F hw hz hb hq
  | negation_intro a =>
    refine quoted_propositional hZ test ⟨9, by decide⟩ (fun _ : Fin 1 => a)
      (implicationTemplate (implicationTemplate (.hole 1) (.leaf 0)) (negationTemplate (.hole 1)))
      rfl (by decide) rfl w z b F hw hz hb hq
  | negation_elimination a =>
    refine quoted_propositional hZ test ⟨10, by decide⟩ (fun _ : Fin 1 => a)
      (implicationTemplate (.hole 1) (implicationTemplate (negationTemplate (.hole 1)) (.leaf 0)))
      rfl (by decide) rfl w z b F hw hz hb hq
  | conjunction_intro a c =>
    refine quoted_propositional hZ test ⟨11, by decide⟩ (fun i : Fin 2 => [a,c][i])
      (implicationTemplate (.hole 1) (implicationTemplate (.hole 2) (conjunctionTemplate (.hole 1) (.hole 2))))
      rfl (by decide) rfl w z b F hw hz hb hq
  | conjunction_elim_left a c =>
    refine quoted_propositional hZ test ⟨12, by decide⟩ (fun i : Fin 2 => [a,c][i])
      (implicationTemplate (conjunctionTemplate (.hole 1) (.hole 2)) (.hole 1)) rfl (by decide) rfl w z b F hw hz hb hq
  | conjunction_elim_right a c =>
    refine quoted_propositional hZ test ⟨13, by decide⟩ (fun i : Fin 2 => [a,c][i])
      (implicationTemplate (conjunctionTemplate (.hole 1) (.hole 2)) (.hole 2)) rfl (by decide) rfl w z b F hw hz hb hq
  | disjunction_intro_left a c =>
    refine quoted_propositional hZ test ⟨14, by decide⟩ (fun i : Fin 2 => [a,c][i])
      (implicationTemplate (.hole 1) (disjunctionTemplate (.hole 1) (.hole 2))) rfl (by decide) rfl w z b F hw hz hb hq
  | disjunction_intro_right a c =>
    refine quoted_propositional hZ test ⟨15, by decide⟩ (fun i : Fin 2 => [a,c][i])
      (implicationTemplate (.hole 2) (disjunctionTemplate (.hole 1) (.hole 2))) rfl (by decide) rfl w z b F hw hz hb hq
  | disjunction_elimination a c d =>
    refine quoted_propositional hZ test ⟨16, by decide⟩ (fun i : Fin 3 => [a,c,d][i])
      (implicationTemplate (implicationTemplate (.hole 1) (.hole 3))
        (implicationTemplate (implicationTemplate (.hole 2) (.hole 3))
          (implicationTemplate (disjunctionTemplate (.hole 1) (.hole 2)) (.hole 3))))
      rfl (by decide) rfl w z b F hw hz hb hq
  | biconditional_intro a c =>
    refine quoted_propositional hZ test ⟨17, by decide⟩ (fun i : Fin 2 => [a,c][i])
      (implicationTemplate (implicationTemplate (.hole 1) (.hole 2))
        (implicationTemplate (implicationTemplate (.hole 2) (.hole 1)) (biconditionalTemplate (.hole 1) (.hole 2))))
      rfl (by decide) rfl w z b F hw hz hb hq
  | biconditional_elim_left a c =>
    refine quoted_propositional hZ test ⟨18, by decide⟩ (fun i : Fin 2 => [a,c][i])
      (implicationTemplate (biconditionalTemplate (.hole 1) (.hole 2)) (implicationTemplate (.hole 1) (.hole 2)))
      rfl (by decide) rfl w z b F hw hz hb hq
  | biconditional_elim_right a c =>
    refine quoted_propositional hZ test ⟨19, by decide⟩ (fun i : Fin 2 => [a,c][i])
      (implicationTemplate (biconditionalTemplate (.hole 1) (.hole 2)) (implicationTemplate (.hole 2) (.hole 1)))
      rfl (by decide) rfl w z b F hw hz hb hq
  | forall_specialization sort body term =>
    cases sort
    exact instantiate_quotation hZ test true body term w z b F hw hz hb hq
  | forall_distribution sort left right =>
    cases sort
    exact forall_distribution_quotation hZ test left right w z b F hw hz hb hq
  | vacuous_forall sort body =>
    cases sort
    exact vacuous_quotation hZ test body w z b F hw hz hb hq
  | exists_introduction sort body term =>
    cases sort
    exact instantiate_quotation hZ test false body term w z b F hw hz hb hq
  | exists_elimination sort body conclusion =>
    cases sort
    exact exists_elimination_quotation hZ test body conclusion w z b F hw hz hb hq
  | equality_substitution sort left right body =>
    cases sort
    exact equality_substitution_quotation hZ test left right body w z b F hw hz hb hq
  | equality_reflexivity term =>
    rename_i sort
    cases sort
    exact reflexivity_quotation hZ test term w z b F hw hz hb hq

theorem logical_quotation_kernel_certificate {m} {free : PureSyntaxQuotation.Ctx}
    (target : Bool) {φ : PureSyntaxQuotation.Fm [] free}
    (cert : HilbertBaseAxiom YesMetaZFC.SetTheory.signature φ) (w z b F : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((omega w).conj ((empty z).conj
        ((SyntaxNumeralSyntax.numeral free.length b).conj (PureQuotationSyntax.formula φ w F)))).imp
        (InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w z b F)).close) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let H := (omega w).conj ((empty z).conj
    ((SyntaxNumeralSyntax.numeral free.length b).conj (PureQuotationSyntax.formula φ w F)))
  have h : Derives (Context.add H (SetLanguage.ZF.at m)) H := .hyp (Or.inl rfl)
  exact from_logical_quotation (ZFContext.add (ZFContext.source_ZF m) _) (OriginalAxiomCodeTest.test target) cert
    w z b F (.conjL h) (.conjL (.conjR h)) (.conjL (.conjR (.conjR h))) (.conjR (.conjR (.conjR h)))

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
