import PPAC.Migration.SchemaClosureQuotation
import PPAC.Migration.Internal.HornExprStructural

/-! Consume the EXISTING original finite schema quotation identities in the
object kernel. Syntax/body indices remain external; every run-time code and
intermediate field is an object variable. No uniform Con claim is made. -/
namespace PPAC.Migration.SchemaTemplateQuotation
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation.ObjectTreeTemplate (Template)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)
attribute [local irreducible] NaturalRecursionSyntax.matrix
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature

private def Correct {n} (inputs : Fin n → Tree) (e : Expr n) (t : Tree) : Prop :=
  ∀ {m} {Γ : Context m}, ZFContext.Evidence Γ → ∀ (w y : Fin m) (env : Fin n → Fin m),
    Derives Γ (omega w) → (∀ i, Derives Γ (OriginalTreeQuotationSyntax.tree (inputs i) w (env i))) →
    Derives Γ (OriginalTreeQuotationSyntax.tree t w y) → Derives Γ (graph e w env y)

private def ForestCorrect {n} (inputs : Fin n → Tree) (es : List (Expr n)) (ts : List Tree) : Prop :=
  ∀ {m} {Γ : Context m}, ZFContext.Evidence Γ → ∀ (w y : Fin m) (env : Fin n → Fin m),
    Derives Γ (omega w) → (∀ i, Derives Γ (OriginalTreeQuotationSyntax.tree (inputs i) w (env i))) →
    Derives Γ (OriginalTreeQuotationSyntax.forest ts w y) → Derives Γ (graph (Expr.list es) w env y)

private theorem variable_correct {n} (inputs : Fin n → Tree) (i : Fin n) : Correct inputs (.var i) (inputs i) := by
  intro m Γ hZ w y env hw he hy
  exact .conjI (OriginalTreeQuotationProperties.tree_range hZ _ w (env i) hw (he i))
    (OriginalTreeQuotationUnique.tree_unique hZ _ w y (env i) hw hy (he i))

private theorem forest_nil {n} (inputs : Fin n → Tree) : ForestCorrect inputs [] [] := by
  intro m Γ hZ w y env hw he hy
  exact HornExprStructural.nil_graph w y env (of_eq (by simp only [OriginalTreeQuotationSyntax.forest]) hy)

private theorem forest_cons {n} (inputs : Fin n → Tree) (e : Expr n) (es : List (Expr n)) (t : Tree) (ts : List Tree)
    (hh : Correct inputs e t) (ht : ForestCorrect inputs es ts) : ForestCorrect inputs (e::es) (t::ts) := by
  intro m Γ hZ w y env hw he hy
  let B := OriginalTreeQuotationSyntax.consBody t ts w y
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ (of_eq (by simp only [B,OriginalTreeQuotationSyntax.forest,OriginalTreeQuotationSyntax.consBody,OriginalTreeQuotationSyntax.consState]) hy)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have he2 (i : Fin n) : Derives Δ (OriginalTreeQuotationSyntax.tree (inputs i) w.castSucc.castSucc (env i).castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,OriginalTreeQuotationSyntax.tree_rename]) (SyntaxRenameBinders.under_2 (he i) B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hh2 := hh hZ2 w.castSucc.castSucc (Fin.last m).castSucc (fun i => (env i).castSucc.castSucc) hw2 he2 (.conjL hB)
  have ht2 := ht hZ2 w.castSucc.castSucc (Fin.last (m+1)) (fun i => (env i).castSucc.castSucc) hw2 he2 (.conjL (.conjR hB))
  exact of_eq (by simp only [Formula.raise,graph_rename,Expr.list,YesMetaZFC.Automation.ObjectSyntaxTransform.cons])
    (HornExprStructural.cons_graph e (Expr.list es) _ _ _ _ _ hh2 ht2 (.conjR (.conjR hB)))

private theorem node_correct {n} (inputs : Fin n → Tree) (tag : Nat) (es : List (Expr n)) (ts : List Tree)
    (ht : ForestCorrect inputs es ts) : Correct inputs (.node (.literal tag) es) (.node tag ts) := by
  intro m Γ hZ w y env hw he hy
  let B := OriginalTreeQuotationSyntax.nodeBody tag ts w y
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ (of_eq (by simp only [B,OriginalTreeQuotationSyntax.tree,OriginalTreeQuotationSyntax.nodeBody,OriginalTreeQuotationSyntax.nodeState]) hy)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have he2 (i : Fin n) : Derives Δ (OriginalTreeQuotationSyntax.tree (inputs i) w.castSucc.castSucc (env i).castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,OriginalTreeQuotationSyntax.tree_rename]) (SyntaxRenameBinders.under_2 (he i) B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht2 := ht hZ2 w.castSucc.castSucc (Fin.last m).castSucc (fun i => (env i).castSucc.castSucc) hw2 he2 (.conjL (.conjR hB))
  exact of_eq (by simp only [Formula.raise,graph_rename,Expr.node])
    (HornExprStructural.raw_graph (.literal tag) (Expr.list es) _ _ _ _ _ (.conjL hB) ht2 (.conjR (.conjR hB)))

attribute [local irreducible] Correct ForestCorrect
private theorem raw_template_correct {n} (inputs : Fin n → Tree) (shape : Template n) :
    Correct inputs shape.expr (shape.plug inputs) := by
  induction shape with
  | hole i => exact variable_correct inputs i
  | leaf tag => exact node_correct inputs tag [] [] (forest_nil inputs)
  | unary tag body ih => exact node_correct inputs tag _ _ (forest_cons inputs _ _ _ _ ih (forest_nil inputs))
  | binary tag left right ih ihR =>
    exact node_correct inputs tag _ _
      (forest_cons inputs _ _ _ _ ih (forest_cons inputs _ _ _ _ ihR (forest_nil inputs)))

-- The same membership-field adaptation as the already accepted coreProgram.
-- Raw term children keep the ORIGINAL Template.expr/plug.
private def pureProgram {n} : Template n → Expr n
  | .hole i => .var i
  | .leaf tag => .node (.literal tag) []
  | .unary tag body => .node (.literal tag) [pureProgram body]
  | .binary tag left right => if tag = 2 then
      .node (.literal 2) [(.node (.literal 0) []),left.expr,right.expr]
    else .node (.literal tag) [pureProgram left,pureProgram right]

private def purePlug {n} (inputs : Fin n → Tree) : Template n → Tree
  | .hole i => inputs i
  | .leaf tag => .node tag []
  | .unary tag body => .node tag [purePlug inputs body]
  | .binary tag left right => if tag = 2 then
      .node 2 [(.node 0 []),left.plug inputs,right.plug inputs]
    else .node tag [purePlug inputs left,purePlug inputs right]

private theorem pure_template_correct {n} (inputs : Fin n → Tree) (shape : Template n) :
    Correct inputs (pureProgram shape) (purePlug inputs shape) := by
  induction shape with
  | hole i => exact variable_correct inputs i
  | leaf tag => exact node_correct inputs tag [] [] (forest_nil inputs)
  | unary tag body ih => exact node_correct inputs tag _ _ (forest_cons inputs _ _ _ _ ih (forest_nil inputs))
  | binary tag left right ih ihR =>
    by_cases h : tag = 2
    · subst tag
      exact node_correct inputs 2 _ _ (forest_cons inputs _ _ _ _
        (node_correct inputs 0 [] [] (forest_nil inputs))
        (forest_cons inputs _ _ _ _ (raw_template_correct inputs left)
          (forest_cons inputs _ _ _ _ (raw_template_correct inputs right) (forest_nil inputs))))
    · simpa only [pureProgram,purePlug,if_neg h] using node_correct inputs tag _ _
        (forest_cons inputs _ _ _ _ ih (forest_cons inputs _ _ _ _ ihR (forest_nil inputs)))
attribute [local semireducible] Correct ForestCorrect

open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
open YesMetaZFC.SetTheory.Definitional.Project (fo_formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC

private theorem pure_value {n} (inputs : Fin n → Tree) (shape : Template n) :
    IntrinsicQuotation.treeValue (purePlug inputs shape) =
      (pureProgram shape).eval (fun i => IntrinsicQuotation.treeValue (inputs i)) := by
  induction shape with
  | hole i => rfl
  | leaf tag => simp only [purePlug,pureProgram,Expr.node_eval,Expr.eval,List.map_nil,
      IntrinsicQuotation.treeValue,IntrinsicQuotation.forestValue,
      YesMetaZFC.Automation.ObjectHorn.nodeValue,YesMetaZFC.Automation.ObjectHorn.listValue]
  | unary tag body ih =>
    simp only [purePlug,pureProgram,Expr.node_eval,Expr.eval,List.map_cons,List.map_nil,
      IntrinsicQuotation.treeValue,IntrinsicQuotation.forestValue,
      YesMetaZFC.Automation.ObjectHorn.nodeValue,YesMetaZFC.Automation.ObjectHorn.listValue,ih]
  | binary tag left right ih ihR =>
    by_cases h : tag = 2
    · subst tag
      simp only [purePlug,pureProgram,↓reduceIte,Expr.node_eval,Expr.eval,List.map_cons,List.map_nil,
        IntrinsicQuotation.treeValue,IntrinsicQuotation.forestValue,
        YesMetaZFC.Automation.ObjectHorn.nodeValue,YesMetaZFC.Automation.ObjectHorn.listValue,
        Template.value_plug]
    · simp only [purePlug,pureProgram,if_neg h,Expr.node_eval,Expr.eval,List.map_cons,List.map_nil,
        IntrinsicQuotation.treeValue,IntrinsicQuotation.forestValue,
        YesMetaZFC.Automation.ObjectHorn.nodeValue,YesMetaZFC.Automation.ObjectHorn.listValue,ih,ihR]

private theorem environment_quotes {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (inputs : Fin n → Tree) (w : Fin m) (env : Fin n → Fin m) (hw : Derives Γ (omega w))
    (he : ∀ i, Derives Γ (OriginalTreeQuotationSyntax.tree (inputs i) w (env i))) :
    Derives Γ (environmentNat n w env) := by
  induction n with
  | zero => exact .impI (.hyp (Or.inl rfl))
  | succ n ih =>
    exact .conjI (OriginalTreeQuotationProperties.tree_range hZ _ w (env 0) hw (he 0))
      (ih (fun i => inputs i.succ) (fun i => env i.succ) (fun i => he i.succ))

private theorem correct_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (inputs : Fin n → Tree) (e : Expr n) (t : Tree) (hc : Correct inputs e t)
    (w y : Fin m) (env : Fin n → Fin m) (hw : Derives Γ (omega w))
    (he : ∀ i, Derives Γ (OriginalTreeQuotationSyntax.tree (inputs i) w (env i))) :
    Derives Γ ((graph e w env y).iff (OriginalTreeQuotationSyntax.tree t w y)) := by
  have hn := environment_quotes hZ inputs w env hw he
  apply Derives.conjI
  · apply Derives.impI
    let E := graph e w env y
    let Ξ := Context.add E Γ
    let P := (Source.Formula.mem (Fin.last m) w.castSucc).conj
      (OriginalTreeQuotationSyntax.tree t w.castSucc (Fin.last m))
    let Δ := Context.add P (Context.image Formula.raise Ξ)
    apply Derives.exE (p := P) (add (OriginalTreeQuotationExistence.tree_exists hZ t w hw) E)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ E) P
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) P)
    have hn1 : Derives Δ (environmentNat n w.castSucc (fun i => (env i).castSucc)) :=
      of_eq (environmentNat_rename n w env Fin.castSucc) (under (add hn E) P)
    have he1 (i : Fin n) : Derives Δ (OriginalTreeQuotationSyntax.tree (inputs i) w.castSucc (env i).castSucc) :=
      of_eq (OriginalTreeQuotationSyntax.tree_rename _ w (env i) Fin.castSucc) (under (add (he i) E) P)
    have hC := hc hZ1 w.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 he1 (.conjR hP)
    have hE : Derives Ξ E := .hyp (Or.inl rfl)
    have hE1 := of_eq (graph_rename e w y env Fin.castSucc) (under hE P)
    have hEq := HornExprUnique.unique hZ1 e w.castSucc (Fin.last m) y.castSucc (fun i => (env i).castSucc) hw1 hn1 hC hE1
    have ho := OriginalQuotationValue.tree_output_subst t w.castSucc (Fin.last m) y.castSucc hEq (.conjR hP)
    exact of_eq (OriginalTreeQuotationSyntax.tree_rename t w y Fin.castSucc).symm ho
  · apply Derives.impI
    exact hc (ZFContext.add hZ _) w y env (add hw _) (fun i => add (he i) _) (.hyp (Or.inl rfl))

private theorem separationCore_closed {k} (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema k) :
    (YesMetaZFC.SetTheory.Axioms.Schema.separationCore schema).FreeClosed :=
  (YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_forallClosure _).mp
    (YesMetaZFC.SetTheory.Axioms.Schema.separation schema).freeClosed

private theorem collectionCore_closed {k} (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema k) :
    (YesMetaZFC.SetTheory.Axioms.Schema.collectionCore schema).FreeClosed :=
  (YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_forallClosure _).mp
    (YesMetaZFC.SetTheory.Axioms.Schema.collection schema).freeClosed

def separationInputs {k} (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema k) : Fin 3 → Tree :=
  fun _ => PureSyntaxQuotation.formulaTree (fo_formula
    (schema.body.rename YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo)
    (by simpa only [YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_rename] using schema.freeClosed))

def collectionInputs {k} (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema k) : Fin 3 → Tree :=
  fun i => if i.val = 0 then PureSyntaxQuotation.formulaTree (fo_formula
    (schema.body.rename YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne)
    (by simpa only [YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_rename] using schema.freeClosed))
  else PureSyntaxQuotation.formulaTree (fo_formula
    (schema.body.rename YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo)
    (by simpa only [YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_rename] using schema.freeClosed))

private theorem separation_tree {k} (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema k) :
    purePlug (separationInputs schema) SchemaTemplate.separation =
      PureSyntaxQuotation.formulaTree (fo_formula (YesMetaZFC.SetTheory.Axioms.Schema.separationCore schema) (separationCore_closed schema)) := by
  apply IntrinsicQuotation.treeValue_injective
  rw [pure_value]
  exact SchemaAxiomAssembly.separation_quotation schema

private theorem collection_tree {k} (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema k) :
    purePlug (collectionInputs schema) SchemaTemplate.collection =
      PureSyntaxQuotation.formulaTree (fo_formula (YesMetaZFC.SetTheory.Axioms.Schema.collectionCore schema) (collectionCore_closed schema)) := by
  apply IntrinsicQuotation.treeValue_injective
  rw [pure_value]
  exact SchemaAxiomAssembly.collection_quotation schema

/-- Consume the EXISTING exact native Separation template identity. -/
theorem separation_core_iff {m k} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema k) (w y : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w))
    (he : ∀ i, Derives Γ (OriginalTreeQuotationSyntax.tree (separationInputs schema i) w (env i))) :
    Derives Γ ((graph (SchemaAxiomAssembly.coreProgram false) w env y).iff
      (PureQuotationSyntax.formula (fo_formula (YesMetaZFC.SetTheory.Axioms.Schema.separationCore schema) (separationCore_closed schema)) w y)) := by
  have h := correct_iff hZ (separationInputs schema) (pureProgram SchemaTemplate.separation)
    (purePlug (separationInputs schema) SchemaTemplate.separation)
    (pure_template_correct (separationInputs schema) SchemaTemplate.separation) w y env hw he
  rw [separation_tree] at h
  exact of_eq (by rfl) h

/-- Consume the EXISTING exact native Collection template identity. -/
theorem collection_core_iff {m k} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema k) (w y : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w))
    (he : ∀ i, Derives Γ (OriginalTreeQuotationSyntax.tree (collectionInputs schema i) w (env i))) :
    Derives Γ ((graph (SchemaAxiomAssembly.coreProgram true) w env y).iff
      (PureQuotationSyntax.formula (fo_formula (YesMetaZFC.SetTheory.Axioms.Schema.collectionCore schema) (collectionCore_closed schema)) w y)) := by
  have h := correct_iff hZ (collectionInputs schema) (pureProgram SchemaTemplate.collection)
    (purePlug (collectionInputs schema) SchemaTemplate.collection)
    (pure_template_correct (collectionInputs schema) SchemaTemplate.collection) w y env hw he
  rw [collection_tree] at h
  exact of_eq (by rfl) h

private theorem assembled_tree_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (collection : Bool) (inputs : Fin 3 → Tree) (core : Tree)
    (hc : Correct inputs (SchemaAxiomAssembly.coreProgram collection) core)
    (w count y : Fin m) (env : Fin 3 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral n count))
    (he : ∀ i, Derives Γ (OriginalTreeQuotationSyntax.tree (inputs i) w (env i))) :
    Derives Γ ((SchemaAxiomAssembly.assembled collection w count env y).iff
      (OriginalTreeQuotationSyntax.tree (SchemaClosureQuotation.wrapped n core) w y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := SchemaAxiomAssembly.assembled collection w count env y
    let P := (Source.Formula.mem (Fin.last m) w.castSucc).conj
      ((graph (SchemaAxiomAssembly.coreProgram collection) w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj
        (SyntaxUnaryIterationSyntax.forallClosure w.castSucc (Fin.last m) count.castSucc y.castSucc))
    let Δ := Context.add P (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := P) (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl))
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ E) P
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) P)
    have hn1 : Derives Δ (SyntaxNumeralSyntax.numeral n count.castSucc) :=
      of_eq (SyntaxNumeralSyntax.numeral_rename n count Fin.castSucc) (under (add hn E) P)
    have he1 (i : Fin 3) : Derives Δ (OriginalTreeQuotationSyntax.tree (inputs i) w.castSucc (env i).castSucc) :=
      of_eq (OriginalTreeQuotationSyntax.tree_rename _ w (env i) Fin.castSucc) (under (add (he i) E) P)
    have ha := Derives.impE (.conjL (correct_iff hZ1 inputs _ core hc w.castSucc (Fin.last m)
      (fun i => (env i).castSucc) hw1 he1)) (.conjL (.conjR hP))
    have ho := Derives.impE (.conjL (SchemaClosureQuotation.tree_iff hZ1 n core w.castSucc
      (Fin.last m) count.castSucc y.castSucc hw1 hn1 ha)) (.conjR (.conjR hP))
    exact of_eq (OriginalTreeQuotationSyntax.tree_rename _ w y Fin.castSucc).symm ho
  · apply Derives.impI
    let E := OriginalTreeQuotationSyntax.tree (SchemaClosureQuotation.wrapped n core) w y
    let P := (Source.Formula.mem (Fin.last m) w.castSucc).conj (OriginalTreeQuotationSyntax.tree core w.castSucc (Fin.last m))
    let Δ := Context.add P (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := P) (add (OriginalTreeQuotationExistence.tree_exists hZ core w hw) E)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ E) P
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) P)
    have hn1 : Derives Δ (SyntaxNumeralSyntax.numeral n count.castSucc) :=
      of_eq (SyntaxNumeralSyntax.numeral_rename n count Fin.castSucc) (under (add hn E) P)
    have he1 (i : Fin 3) : Derives Δ (OriginalTreeQuotationSyntax.tree (inputs i) w.castSucc (env i).castSucc) :=
      of_eq (OriginalTreeQuotationSyntax.tree_rename _ w (env i) Fin.castSucc) (under (add (he i) E) P)
    have hG := hc hZ1 w.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 he1 (.conjR hP)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hE1 := of_eq (OriginalTreeQuotationSyntax.tree_rename _ w y Fin.castSucc) (under hE P)
    have hC := Derives.impE (.conjR (SchemaClosureQuotation.tree_iff hZ1 n core w.castSucc
      (Fin.last m) count.castSucc y.castSucc hw1 hn1 (.conjR hP))) hE1
    have ho : Derives Δ (SchemaAxiomAssembly.assembled collection w.castSucc count.castSucc (fun i => (env i).castSucc) y.castSucc) := by
      apply Derives.exI (Fin.last m)
      exact of_eq (by simp only [Formula.instantiate,Formula.rename,graph_rename,
        SyntaxUnaryIterationSyntax.forallClosure_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq])
        (.conjI (.conjL hP) (.conjI hG hC))
    exact of_eq (SchemaAxiomAssembly.assembled_rename collection w count y env Fin.castSucc).symm ho

/-- The EXISTING actual finite shell and whole closure yield exactly the
ORIGINAL native Separation sentence. Matrix quotation is an explicit parent. -/
theorem separation_iff {m k} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema k) (w count y : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral k count))
    (he : ∀ i, Derives Γ (OriginalTreeQuotationSyntax.tree (separationInputs schema i) w (env i))) :
    Derives Γ ((SchemaAxiomAssembly.assembled false w count env y).iff
      (PureQuotationSyntax.formula (NativeAxiomCertificateData.sentence (.separation schema)) w y)) := by
  have hc : Correct (separationInputs schema) (SchemaAxiomAssembly.coreProgram false)
      (purePlug (separationInputs schema) SchemaTemplate.separation) := pure_template_correct _ _
  have h := assembled_tree_iff hZ false (separationInputs schema) _ hc w count y env hw hn he
  rw [separation_tree,SchemaClosureQuotation.original_closure_tree] at h
  exact of_eq (by rfl) h

/-- Both distinct original Collection matrix occurrences are retained. -/
theorem collection_iff {m k} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema k) (w count y : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral k count))
    (he : ∀ i, Derives Γ (OriginalTreeQuotationSyntax.tree (collectionInputs schema i) w (env i))) :
    Derives Γ ((SchemaAxiomAssembly.assembled true w count env y).iff
      (PureQuotationSyntax.formula (NativeAxiomCertificateData.sentence (.collection schema)) w y)) := by
  have hc : Correct (collectionInputs schema) (SchemaAxiomAssembly.coreProgram true)
      (purePlug (collectionInputs schema) SchemaTemplate.collection) := pure_template_correct _ _
  have h := assembled_tree_iff hZ true (collectionInputs schema) _ hc w count y env hw hn he
  rw [collection_tree,SchemaClosureQuotation.original_closure_tree] at h
  exact of_eq (by rfl) h

private def matrixQuotes {m} (inputs : Fin 3 → Tree) (w : Fin m) (env : Fin 3 → Fin m) : Source.Formula m :=
  (OriginalTreeQuotationSyntax.tree (inputs 0) w (env 0)).conj
    ((OriginalTreeQuotationSyntax.tree (inputs 1) w (env 1)).conj (OriginalTreeQuotationSyntax.tree (inputs 2) w (env 2)))

private theorem matrixQuotes_at {m} {Γ : Context m} (inputs : Fin 3 → Tree) (w : Fin m) (env : Fin 3 → Fin m)
    (he : Derives Γ (matrixQuotes inputs w env)) (i : Fin 3) :
    Derives Γ (OriginalTreeQuotationSyntax.tree (inputs i) w (env i)) := by
  exact Fin.cases (.conjL he) (fun j => Fin.cases (.conjL (.conjR he))
    (fun k => Fin.cases (.conjR (.conjR he)) (fun z => Fin.elim0 z) k) j) i

def separationSentence {m k} (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema k)
    (w count y : Fin m) (env : Fin 3 → Fin m) : Source.Sentence :=
  ((omega w).imp ((SyntaxNumeralSyntax.numeral k count).imp
    ((matrixQuotes (separationInputs schema) w env).imp
      ((SchemaAxiomAssembly.assembled false w count env y).iff
        (PureQuotationSyntax.formula (NativeAxiomCertificateData.sentence (.separation schema)) w y))))).close

def collectionSentence {m k} (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema k)
    (w count y : Fin m) (env : Fin 3 → Fin m) : Source.Sentence :=
  ((omega w).imp ((SyntaxNumeralSyntax.numeral k count).imp
    ((matrixQuotes (collectionInputs schema) w env).imp
      ((SchemaAxiomAssembly.assembled true w count env y).iff
        (PureQuotationSyntax.formula (NativeAxiomCertificateData.sentence (.collection schema)) w y))))).close

theorem separation_source_certificate {m k} (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema k)
    (w count y : Fin m) (env : Fin 3 → Fin m) :
    Derives (Source.SetLanguage.ZF.at 0) (separationSentence schema w count y env) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (matrixQuotes (separationInputs schema) w env)
    (Context.add (SyntaxNumeralSyntax.numeral k count) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _
  exact separation_iff hZ schema w count y env (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (matrixQuotes_at _ w env (.hyp (Or.inl rfl)))

theorem collection_source_certificate {m k} (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema k)
    (w count y : Fin m) (env : Fin 3 → Fin m) :
    Derives (Source.SetLanguage.ZF.at 0) (collectionSentence schema w count y env) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (matrixQuotes (collectionInputs schema) w env)
    (Context.add (SyntaxNumeralSyntax.numeral k count) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _
  exact collection_iff hZ schema w count y env (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (matrixQuotes_at _ w env (.hyp (Or.inl rfl)))

theorem separation_kernel_certificate {m k} (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema k)
    (w count y : Fin m) (env : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (separationSentence schema w count y env)) :=
  ZFReplay.replay (TheoryTransport.sentence (separation_source_certificate schema w count y env))

theorem collection_kernel_certificate {m k} (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema k)
    (w count y : Fin m) (env : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (collectionSentence schema w count y env)) :=
  ZFReplay.replay (TheoryTransport.sentence (collection_source_certificate schema w count y env))

end PPAC.Migration.SchemaTemplateQuotation
