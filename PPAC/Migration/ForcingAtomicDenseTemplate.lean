import PPAC.Migration.ForcingAtomicCode
import PPAC.Migration.ForcingDensityInstantiation
import PPAC.Migration.ForcingGuardOpening
import PPAC.Migration.Internal.AtomicProgramAlignment
import PPAC.Migration.ForcingAtomicMono
import PPAC.Migration.ForcingAtomicMonoImages
import PPAC.Migration.ForcingAtomicMonoTemplate
import PPAC.Migration.ForcingPreorderCode
import PPAC.Migration.ForcingRelationSource
import PPAC.Migration.NativeProofQuotation

/-! The atomic branches of the original force_of_dense. Use the same R, P,
p and atom template as the original compiler. The density premise uses the
original order of the two bound conditions and the same atom at r. -/
namespace PPAC.Migration.ForcingAtomicDenseTemplate
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open SetTheory.Definitional.Project (fo_bound_context fo_bound_variable)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option maxRecDepth 32768

private abbrev params {k} (i : Fin k) : Fin (k+4) := i.castSucc.castSucc.castSucc.castSucc
private abbrev carrier (k : Nat) : Fin (k+4) := (Fin.last k).castSucc.castSucc.castSucc
private abbrev condition (k : Nat) : Fin (k+4) := (Fin.last (k+1)).castSucc.castSucc
private abbrev leftName (k : Nat) : Fin (k+4) := (Fin.last (k+2)).castSucc
private abbrev rightName (k : Nat) : Fin (k+4) := Fin.last (k+3)

private theorem row_rename {m l} (g x y a b : Fin m) (r : Fin m → Fin l) :
    (ForcingAtomicStep.row g x y a b).rename r = ForcingAtomicStep.row (r g) (r x) (r y) (r a) (r b) := by
  simp only [ForcingAtomicStep.row, Source.Formula.rename, GraphSyntax.edge_original, GraphSyntax.edge_rename,
    PairSyntax.ordered_rename, Source.Formula.liftRen, Fin.lastCases_castSucc, Fin.lastCases_last]

private theorem query_rename {m l} (equality : Bool) (g x y p : Fin m) (r : Fin m → Fin l) :
    (ForcingAtomicStep.query equality g x y p).rename r =
      ForcingAtomicStep.query equality (r g) (r x) (r y) (r p) := by
  cases equality <;>
    simp only [ForcingAtomicStep.query, Source.Formula.rename, row_rename, Bool.false_eq_true, if_false, if_true,
      Source.Formula.liftRen, Fin.lastCases_castSucc, Fin.lastCases_last]

private theorem equation_rename {k m l} (R : Source.Formula (k+2)) (params : Fin k → Fin m)
    (P g x y output : Fin m) (r : Fin m → Fin l) :
    (ForcingAtomicStep.equation R params P g x y output).rename r =
      ForcingAtomicStep.equation R (fun i => r (params i)) (r P) (r g) (r x) (r y) (r output) := by
  simp only [ForcingAtomicStep.equation, ForcingAtomicStep.memBody, ForcingAtomicStep.eqBody,
    ForcingAtomicStep.eqHalf, Source.Formula.iff, Source.Formula.rename, GraphSyntax.edge_original,
    GraphSyntax.edge_rename, PairSyntax.ordered_rename, ReplacementPredicates.rel_rename,
    ReplacementPredicates.paramsUp, query_rename, Source.Formula.liftRen, Fin.lastCases_castSucc,
    Fin.lastCases_last]

private theorem lookup_rename {m l} (g x y output : Fin m) (r : Fin m → Fin l) :
    (ForcingAtomicGraphs.lookup g x y output).rename r =
      ForcingAtomicGraphs.lookup (r g) (r x) (r y) (r output) := by
  simp only [ForcingAtomicGraphs.lookup, Source.Formula.rename, GraphSyntax.edge_original, GraphSyntax.edge_rename,
    PairSyntax.ordered_rename, Source.Formula.liftRen, Fin.lastCases_castSucc, Fin.lastCases_last]

private theorem below_rename {m l} (swap : Bool) (g x y : Fin m) (r : Fin m → Fin l) :
    (ForcingAtomicGraphs.below swap g x y).rename r = ForcingAtomicGraphs.below swap (r g) (r x) (r y) := by
  cases swap <;>
    simp only [ForcingAtomicGraphs.below, Source.Formula.rename, GraphSyntax.edge_original,
      GraphSyntax.edge_rename, lookup_rename, Bool.false_eq_true, if_false, if_true, Source.Formula.liftRen,
      Fin.lastCases_castSucc, Fin.lastCases_last]

private theorem forces_rename {k m l} (equality : Bool) (R : Source.Formula (k+2)) (params : Fin k → Fin m)
    (P x y p : Fin m) (r : Fin m → Fin l) :
    (ForcingAtomicRelations.forces equality R params P x y p).rename r =
      ForcingAtomicRelations.forces equality R (fun i => r (params i)) (r P) (r x) (r y) (r p) := by
  simp only [ForcingAtomicRelations.forces, ForcingAtomicGraphs.good, ForcingAtomicGraphs.covered,
    Source.Formula.rename, lookup_rename, below_rename, equation_rename, query_rename,
    ReplacementPredicates.paramsUp, Source.Formula.liftRen, Fin.lastCases_castSucc, Fin.lastCases_last]

/-- The scope under the original q and r binders preserves R, P and the two
names. Only the original condition slot is replaced by the witness r. -/
def witnessMap (k : Nat) : Fin (k+4) → Fin (k+6) :=
  Fin.lastCases (rightName k).castSucc.castSucc
    (Fin.lastCases (leftName k).castSucc.castSucc
      (Fin.lastCases (Fin.last (k+5)) (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)))

theorem witness_atom {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) :
    (ForcingAtomicCode.sourceTemplate equality R).rename (witnessMap k) =
      ForcingAtomicRelations.forces equality R (fun i => (params i).castSucc.castSucc)
        (carrier k).castSucc.castSucc (leftName k).castSucc.castSucc (rightName k).castSucc.castSucc (Fin.last (k+5)) := by
  simp only [ForcingAtomicCode.sourceTemplate, forces_rename, witnessMap, params, carrier, leftName, rightName,
    Fin.lastCases_last, Fin.lastCases_castSucc]

private def nameSlot (k : Nat) : Fin 2 → Fin (k+4) :=
  Fin.cases (rightName k) (fun _ => leftName k)

/-- The same native atomic template serves both the conclusion at p and the
density witness at r. Its two bound name slots stay in the compiler order. -/
theorem atom_instance {k : Nat} {bound free : Syntax.Ctx} (equality : Bool) (R : Source.Formula (k+2))
    (env : Fin (k+4) → Syntax.Tm bound free) :
    (ForcingAtomicCode.template equality R).substituteMapped
      (ForcingRelationSource.mapping (fun i => env (nameSlot k i)))
      (ForcingRelationSource.mapping (fun i : Fin (k+2) => env i.castSucc.castSucc)) =
      Syntax.formula env (ForcingAtomicCode.sourceTemplate equality R) := by
  rw [ForcingAtomicCode.template_as_source, Syntax.substitute]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [ForcingAtomicCode.sourceRoles, Fin.lastCases_last, Term.substituteMapped] <;> rfl
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [ForcingAtomicCode.sourceRoles, Fin.lastCases_castSucc, Fin.lastCases_last,
        Term.substituteMapped] <;> rfl
    · simp only [ForcingAtomicCode.sourceRoles, Fin.lastCases_castSucc, Term.substituteMapped,
        ForcingRelationSource.mapping_at]

theorem witness_native {k : Nat} {bound free : Syntax.Ctx} (equality : Bool) (R : Source.Formula (k+2))
    (env : Fin (k+6) → Syntax.Tm bound free) :
    (ForcingAtomicCode.template equality R).substituteMapped
      (ForcingRelationSource.mapping (fun i => env (witnessMap k (nameSlot k i))))
      (ForcingRelationSource.mapping (fun i : Fin (k+2) => env (witnessMap k i.castSucc.castSucc))) =
      Syntax.formula env ((ForcingAtomicCode.sourceTemplate equality R).rename (witnessMap k)) := by
  rw [Syntax.rename]
  exact atom_instance equality R (fun i => env (witnessMap k i))

open ReplacementPredicates (paramsUp)

def densePremise {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) : Source.Formula (k+4) :=
  let q := Fin.last (k+4)
  let r := Fin.last (k+5)
  .all ((Source.Formula.mem q (carrier k).castSucc).imp
    ((ReplacementPredicates.rel R (paramsUp params) q (condition k).castSucc).imp
      (.ex ((Source.Formula.mem r (carrier k).castSucc.castSucc).conj
        ((ReplacementPredicates.rel R (paramsUp (paramsUp params)) r q.castSucc).conj
          ((ForcingAtomicCode.sourceTemplate equality R).rename (witnessMap k)))))))

theorem densePremise_eq {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) :
    densePremise equality R =
      ForcingAtomicBasic.dense equality R params (carrier k) (leftName k) (rightName k) (condition k) := by
  simp only [densePremise, ForcingAtomicBasic.dense, witness_atom]

universe u

private theorem dense_at {M : FirstOrder.Structure.{0,0,0,u} ℒ} {k : Nat}
    (hM : FirstOrder.Theory.Models M nativeZF) (equality : Bool) (R : Source.Formula (k+2))
    (env : Fin (k+4) → M.Carrier .set)
    (hPre : ForcingAtomicBasic.PreorderOn R (fun i => env (params i)) (env (carrier k)))
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem (env (condition k)) (env (carrier k)))
    (hDense : Source.Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env
      (densePremise equality R)) :
    Source.Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env
      (ForcingAtomicCode.sourceTemplate equality R) := by
  rw [densePremise_eq] at hDense
  have hd := (ForcingAtomicBasic.dense_semantics (M := M) env equality R params
    (carrier k) (leftName k) (rightName k) (condition k)).mp hDense
  apply (ForcingAtomicRelations.forces_semantics (M := M) env equality R params
    (carrier k) (leftName k) (rightName k) (condition k)).mpr
  cases equality with
  | false => exact ForcingAtomicBasic.mem_of_dense hM hPre hp hd
  | true => exact ForcingAtomicBasic.eq_of_dense hM hPre hp hd

open ForcingAtomicMonoTemplate (sourceLeaf)

private def atCondition (k : Nat) : Fin (k+4) → Fin (k+7) :=
  Fin.lastCases 0 (Fin.lastCases 1 (ForcingAtomicMonoTemplate.freeIndex k .newer))

/-- Use the actual q-row of the existing common preorder layout. The
fourth antecedent is density at q in place of the old atomic premise. -/
def layoutSource {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) : Source.Formula (k+7) :=
  (sourceLeaf equality R .preorder).imp ((sourceLeaf equality R .member).imp
    ((sourceLeaf equality R .order).imp (((densePremise equality R).rename (atCondition k)).imp
      (sourceLeaf equality R .newer))))

def layoutFormula {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) :
    PureSyntaxQuotation.Fm [] (fo_bound_context (k+7)) :=
  Syntax.formula (fun i => .fvar (fo_bound_variable i)) (layoutSource equality R)

private theorem layout_proof {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) :
    FirstOrder.Derives nativeZF [] (layoutFormula equality R) := by
  apply NativeProofQuotation.from_source_closure (layoutSource equality R) (ForcingAtomicMonoTemplate.carrier k)
  apply ModelTransfer.derives
  intro M hM
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hPre hMem _ hDense
  let mem := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  let v := fun i => env (atCondition k i)
  have hBase : Source.Formula.Realize mem (fun i => env (ForcingAtomicMonoTemplate.base i))
      (ForcingPreorderCode.source R) :=
    (DefinableMinimaChoice.realize_rename mem (ForcingPreorderCode.source R) ForcingAtomicMonoTemplate.base env).mp hPre
  have hP := (ForcingAtomicBasic.preorder_semantics (M := M)
    (fun i => env (ForcingAtomicMonoTemplate.base i)) R (fun i => i.castSucc.castSucc) (Fin.last k).castSucc).mp hBase
  have hPQ : ForcingAtomicBasic.PreorderOn R (fun i => v (params i)) (v (carrier k)) := by
    simpa only [v, atCondition, ForcingAtomicMonoTemplate.freeIndex, params, carrier,
      Fin.lastCases_castSucc] using hP
  change mem (env 2) (env (ForcingAtomicMonoTemplate.carrier k)) at hMem
  have hMQ : mem (v (condition k)) (v (carrier k)) := by
    simpa only [v, atCondition, ForcingAtomicMonoTemplate.freeIndex, condition, carrier,
      ForcingAtomicMonoTemplate.carrier, Fin.lastCases_castSucc, Fin.lastCases_last] using hMem
  have hd := (DefinableMinimaChoice.realize_rename mem (densePremise equality R) (atCondition k) env).mp hDense
  change Source.Formula.Realize mem env ((ForcingAtomicCode.sourceTemplate equality R).rename (atCondition k))
  exact (DefinableMinimaChoice.realize_rename mem (ForcingAtomicCode.sourceTemplate equality R) (atCondition k) env).mpr
    (dense_at hM equality R v hPQ hMQ hd)

/-- Discharge the instantiated atomic density proof with the original
preorder row and the same conditional Root proof of density. -/
theorem at_instance {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (k+2))
    (w z a b B L N Extra Pre D : Fin m) (H layout : Fin 6 → Fin m) (tails : Fin 5 → Fin m)
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (ha : Source.Derives Γ (SyntaxNumeralSyntax.numeral (k+7) a))
    (hN : Source.Derives Γ (PureQuotationSyntax.formula (layoutFormula equality R) w N))
    (hF : Source.Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B L z a z b N (tails 0)))
    (hCtor : ∀ i : Fin 4, Source.Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w
      (ForcingAtomicMono.heads Pre D H i) (tails i.succ) (tails i.castSucc)))
    (hExtra : Source.Derives Γ (FormulaCodeSyntax.formulaCode w Extra z b))
    (hLayout : Source.Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (hDense : Source.Derives Γ (InternalProofBackground.implication (OriginalAxiomCodeTest.test false) w z b (layout 3) D)) :
    Source.Derives Γ (InternalProofBackground.implication (OriginalAxiomCodeTest.test false) w z b (layout 3) (tails 4)) :=
  ForcingAtomicMono.at_instance hZ (layout_proof equality R) w z a b B L N Extra Pre D H layout tails
    hw hz (of_eq (by rw [List.length_replicate]) ha) hN hF hCtor hExtra hLayout hDense

open InternalProofBackground (implication implication_rename)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
open SyntaxNumeralSyntax (numeral numeral_rename)

private abbrev test : Source.Formula 1 := OriginalAxiomCodeTest.test false

def layoutHead {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) :
    Fin 5 → PureSyntaxQuotation.Fm [] (fo_bound_context (k+7)) :=
  let leaf := ForcingAtomicMonoTemplate.nativeLeaf equality R
  let density := Syntax.formula (fun i => .fvar (fo_bound_variable i))
    ((densePremise equality R).rename (atCondition k))
  Fin.cases (leaf .preorder) (Fin.cases (leaf .member) (Fin.cases (leaf .order)
    (Fin.cases density (fun _ => leaf .newer))))

open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)

private def outerOrderLeaf {k : Nat} (R : Source.Formula (k+2)) :
    PureSyntaxQuotation.Fm (fo_bound_context 1) (fo_bound_context (k+7)) :=
  let env : Fin (k+4) → Syntax.Tm [] (fo_bound_context (k+7)) :=
    fun i => .fvar (fo_bound_variable (atCondition k i))
  Syntax.formula (Syntax.lift env)
    (ReplacementPredicates.rel R (paramsUp params) (Fin.last (k+4)) (condition k).castSucc)

private def outerBoundMap (k : Nat) :
    NativeSubstitutionSyntax.Mapping (fo_bound_context 1) (fo_bound_context 1) (fo_bound_context (k+7)) :=
  ForcingRelationSource.mapping (fun i => .bvar (fo_bound_variable i))

private def outerFreeMap (k : Nat) :
    NativeSubstitutionSyntax.Mapping (fo_bound_context (k+2)) (fo_bound_context 1) (fo_bound_context (k+7)) :=
  ForcingRelationSource.mapping (fun i => .fvar (fo_bound_variable (ForcingAtomicMonoTemplate.freeIndex k .newer i)))

private theorem outer_order_transport {k : Nat} (R : Source.Formula (k+2)) :
    (ForcingGuardCode.template true R).substituteMapped (outerBoundMap k) (outerFreeMap k) = outerOrderLeaf R := by
  rw [ForcingGuardCode.relation_template, Syntax.substitute, outerOrderLeaf]
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, Syntax.rename]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Term.substituteMapped,
      outerFreeMap, ForcingRelationSource.mapping_at, Syntax.lift, atCondition] <;> rfl
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Term.substituteMapped,
        outerBoundMap, Syntax.lift] <;> rfl
    · simp only [Fin.lastCases_castSucc, Term.substituteMapped,
        outerFreeMap, ForcingRelationSource.mapping_at, Syntax.lift, atCondition, paramsUp, params] <;> rfl

/-- The original five leaves with the common-table free roles and the two
density binders in their native order. -/
def densityLeafTree {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) : Fin 5 → Tree :=
  let env : Fin (k+4) → Syntax.Tm [] (fo_bound_context (k+7)) :=
    fun i => .fvar (fo_bound_variable (atCondition k i))
  let q := Fin.last (k+4)
  let r := Fin.last (k+5)
  let atQ := fun p => PureSyntaxQuotation.formulaTree (Syntax.formula (Syntax.lift env) p)
  let atR := fun p => PureSyntaxQuotation.formulaTree (Syntax.formula (Syntax.lift (Syntax.lift env)) p)
  Fin.cases (atQ (.mem q (carrier k).castSucc))
    (Fin.cases (PureSyntaxQuotation.formulaTree (outerOrderLeaf R))
      (Fin.cases (atR (.mem r (carrier k).castSucc.castSucc))
        (Fin.cases (atR (ReplacementPredicates.rel R (paramsUp (paramsUp params)) r q.castSucc))
          (fun _ => atR ((ForcingAtomicCode.sourceTemplate equality R).rename (witnessMap k))))))

private def densityNodes (leaf : Fin 5 → Tree) : Fin 5 → Tree :=
  let rRest : Tree := .node 5 [leaf 3, leaf 4]
  let rBody : Tree := .node 5 [leaf 2, rRest]
  let tail : Tree := .node 10 [rBody]
  let qRest : Tree := .node 7 [leaf 1, tail]
  let qBody : Tree := .node 7 [leaf 0, qRest]
  Fin.cases rRest (Fin.cases rBody (Fin.cases tail (Fin.cases qRest (fun _ => qBody))))

private theorem density_tree {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) :
    PureSyntaxQuotation.formulaTree (layoutHead equality R 3) =
      .node 9 [densityNodes (densityLeafTree equality R) 4] := by
  change PureSyntaxQuotation.formulaTree (Syntax.formula (fun i => .fvar (fo_bound_variable i))
    ((densePremise equality R).rename (atCondition k))) = _
  rw [Syntax.rename]
  rfl

/-- Open the actual quotation consumed by the canonical density proof. The
subtrees are quoted from its literal layout and linked to that same root. -/
theorem with_quoted_shell {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (k+2)) (w D : Fin m)
    (hw : Source.Derives Γ (omega w))
    (hD : Source.Derives Γ (PureQuotationSyntax.formula (layoutHead equality R 3) w D))
    (out : Source.Formula m)
    (use : ∀ {l} {Δ : Source.Context l} (r : Fin m → Fin l) (leaf v : Fin 5 → Fin l),
      ZFContext.Evidence Δ →
      (∀ {F : Source.Formula m}, Source.Derives Γ F → Source.Derives Δ (F.rename r)) →
      (∀ i, Source.Derives Δ (OriginalTreeQuotationSyntax.tree (densityLeafTree equality R i) (r w) (leaf i))) →
      Source.Derives Δ (ForcingDensityInstantiation.rawShell (r w) (r D) leaf v) →
      Source.Derives Δ (out.rename r)) : Source.Derives Γ out := by
  let leaf := densityLeafTree equality R
  let node := densityNodes leaf
  let trees : Fin (5+5) → Tree := Fin.addCases (motive := fun _ => Tree) leaf node
  apply ProjectCompilerQuotation.eliminate_quotations hZ (5+5) trees w hw out
  intro l Δ r xs hZ1 lift hTrees
  let L : Fin 5 → Fin l := fun i => xs (i.castAdd 5)
  let V : Fin 5 → Fin l := fun i => xs (i.natAdd 5)
  let quoted := fun t => OriginalTreeQuotationSyntax.tree t (r w)
  have hLeaf (i : Fin 5) : Source.Derives Δ (quoted (leaf i) (L i)) := by
    simpa only [trees, L, Fin.addCases_left] using hTrees (i.castAdd 5)
  have hNode (i : Fin 5) : Source.Derives Δ (quoted (node i) (V i)) := by
    simpa only [trees, V, Fin.addCases_right] using hTrees (i.natAdd 5)
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hRoot : Source.Derives Δ (quoted (.node 9 [node 4]) (r D)) :=
    of_eq (congrArg (fun t => quoted t (r D)) (density_tree equality R))
      (of_eq (PureQuotationSyntax.formula_rename (layoutHead equality R 3) w D r) (lift hD))
  have unary (tag : Nat) (t : Tree) (x p : Fin l)
      (hx : Source.Derives Δ (quoted t x))
      (hp : Source.Derives Δ (quoted (.node tag [t]) p)) :
      Source.Derives Δ (SyntaxLogicalSyntax.singleCode tag (r w) x p) :=
    OriginalQuotationNodeFields.tree_to_constructor hZ1 tag [t] (r w) p (fun _ => x) hw1
      (.conjI hx (.eqRefl (r w))) hp
  have binary (kind : Fin 4) (t u : Tree) (x y p : Fin l)
      (hx : Source.Derives Δ (quoted t x)) (hy : Source.Derives Δ (quoted u y))
      (hp : Source.Derives Δ (quoted (.node (5+kind.val) [t,u]) p)) :
      Source.Derives Δ (SyntaxLogicalSyntax.binaryCode kind (r w) x y p) :=
    OriginalQuotationNodeFields.tree_to_constructor hZ1 (5+kind.val) [t,u] (r w) p
      (SyntaxAtomSyntax.two x y) hw1 (.conjI hx (.conjI hy (.eqRefl (r w)))) hp
  exact use r L V hZ1 lift hLeaf
    (.conjI (unary 9 (node 4) (V 4) (r D) (hNode 4) hRoot)
      (.conjI (binary 2 (leaf 0) (node 3) (L 0) (V 3) (V 4) (hLeaf 0) (hNode 3) (hNode 4))
        (.conjI (binary 2 (leaf 1) (node 2) (L 1) (V 2) (V 3) (hLeaf 1) (hNode 2) (hNode 3))
          (.conjI (unary 10 (node 1) (V 1) (V 2) (hNode 1) (hNode 2))
            (.conjI (binary 0 (leaf 2) (node 0) (L 2) (V 0) (V 1) (hLeaf 2) (hNode 0) (hNode 1))
              (binary 0 (leaf 3) (leaf 4) (L 3) (L 4) (V 0) (hLeaf 3) (hLeaf 4) (hNode 0)))))))

section MemberGuards

open NativeProofQuotation (eliminate_objects)
open StructuralListFieldSyntax (field field_rename)
open SyntaxCodedMixedBinderSyntax (lifted)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (leaf)

attribute [local irreducible] NaturalRecursionSyntax.matrix
set_option maxHeartbeats 1200000

private theorem member_tree {k : Nat} (equality inner : Bool) (R : Source.Formula (k+2)) :
    densityLeafTree equality R (if inner then 2 else 0) =
      Tree.node 2 ([leaf 0, Tree.node 0 ([leaf 0]), Tree.node 1 ([leaf (k+5)])]) := by
  let j := atCondition k (carrier k)
  have hj : (fo_bound_variable j).index = k+5 := by
    have hv := ProjectNativeRenaming.variable_index (fun _ : Fin 1 => j) (fo_bound_variable 0)
    rw [ProjectNativeRenaming.variable_at] at hv
    simpa [j, atCondition, carrier, ForcingAtomicMonoTemplate.freeIndex, ForcingAtomicMonoTemplate.base] using hv
  cases inner <;>
    simp only [densityLeafTree, Bool.false_eq_true, ↓reduceIte, Syntax.formula, Syntax.lift,
      Fin.lastCases_last, Fin.lastCases_castSucc, Term.weakenBound_fvar, PureSyntaxQuotation.formulaTree,
      PureSyntaxQuotation.argumentTrees, PureSyntaxQuotation.termTree] <;>
    change Tree.node 2 ([leaf 0, Tree.node 0 ([leaf 0]), Tree.node 1 ([leaf (fo_bound_variable j).index])]) = _ <;>
    rw [hj]

private theorem member_of_quote {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (equality inner : Bool) (R : Source.Formula (k+2)) (w z K H a g c b i P V Q Y : Fin m)
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (hi : Source.Derives Γ (numeral (k+5) i))
    (hP : Source.Derives Γ (field w K z P)) (hV : Source.Derives Γ (field w H i V))
    (hQ : Source.Derives Γ (OriginalTreeQuotationSyntax.tree (densityLeafTree equality R (if inner then 2 else 0)) w Q))
    (hY : Source.Derives Γ (substituted w K H a g c b Q Y)) :
    Source.Derives Γ (ForcingMemberGuardOpening.result w P V Y) := by
  let trees : Fin 3 → Tree := Fin.cases (leaf 0)
    (Fin.cases (.node 0 [leaf 0]) (fun _ => .node 1 [leaf (k+5)]))
  apply ProjectCompilerQuotation.eliminate_quotations hZ 3 trees w hw
  intro l Δ r x hZ1 move hTrees
  have hw1 := of_eq (omega_rename w r) (move hw)
  have hz1 := of_eq (empty_rename z r) (move hz)
  have hi1 := of_eq (numeral_rename (k+5) i r) (move hi)
  have hs := OriginalQuotationNodeFields.tree_to_constructor hZ1 0 [] (r w) (x 0)
    Fin.elim0 hw1 (.eqRefl (r w)) (hTrees 0)
  have hX := OriginalQuotationVariableFields.variable_of_tree hZ1 true 0 (r w) (r z) (x 1)
    hw1 hz1 (hTrees 1)
  have hW := OriginalQuotationVariableFields.variable_of_tree hZ1 false (k+5) (r w) (r i) (x 2)
    hw1 hi1 (hTrees 2)
  have hNode := of_eq (congrArg (fun T => OriginalTreeQuotationSyntax.tree T (r w) (r Q))
    (member_tree equality inner R)) (of_eq (OriginalTreeQuotationSyntax.tree_rename _ _ _ _) (move hQ))
  have hMem0 := OriginalQuotationNodeFields.tree_to_constructor hZ1 2
    [leaf 0, Tree.node 0 ([leaf 0]), Tree.node 1 ([leaf (k+5)])] (r w) (r Q) x hw1
    (.conjI (hTrees 0) (.conjI (hTrees 1) (.conjI (hTrees 2) (.eqRefl (r w))))) hNode
  have hArgs : x = SyntaxAtomSyntax.three (x 0) (x 1) (x 2) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
  have hMem : Source.Derives Δ (SyntaxAtomSyntax.memberCode (r w) (x 0) (x 1) (x 2) (r Q)) :=
    of_eq (congrArg (fun t => SyntaxNodeSyntax.constructor 3 2 (r w) t (r Q)) hArgs) hMem0
  apply of_eq (ForcingMemberGuardOpening.result_rename w P V Y r).symm
  exact ForcingRawModalBody.member_atom_at hZ1 (r w) (r z) (r K) (r H) (r a) (r g) (r c) (r b)
    (x 1) (r P) (r i) (r V) (r Q) (r Y) (x 0) (x 2) hw1 hz1 hX
    (of_eq (field_rename w K z P r) (move hP)) (SyntaxNumerals.range hZ1 (k+5) (r w) (r i) hw1 hi1)
    (of_eq (field_rename w H i V r) (move hV)) (.conjI hs (.conjI hW hMem))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (move hY))

private theorem member_results_eq {m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (w P V X Y : Fin m) (hw : Source.Derives Γ (omega w))
    (hX : Source.Derives Γ (ForcingMemberGuardOpening.result w P V X))
    (hY : Source.Derives Γ (ForcingMemberGuardOpening.result w P V Y)) :
    Source.Derives Γ (.equal X Y) := by
  let point {l : Nat} (w P V X sym : Fin l) :=
    (SyntaxAtomSyntax.zeroScalar w sym).conj (SyntaxAtomSyntax.memberCode w sym P V X)
  refine eliminate_objects hZ 1 (fun r t => point (r w) (r P) (r V) (r X) (t 0)) hX (.equal X Y) ?_
  intro l Δ r t hZ1 move hx
  have hy := of_eq (ForcingMemberGuardOpening.result_rename w P V Y r) (move hY)
  have hw1 := of_eq (omega_rename w r) (move hw)
  refine eliminate_objects hZ1 1 (fun s u => point (s (r w)) (s (r P)) (s (r V)) (s (r Y)) (u 0))
    hy (.equal (r X) (r Y)) ?_
  intro l1 Δ1 s u hZ2 move1 hy
  have hx1 : Source.Derives Δ1 (point (s (r w)) (s (r P)) (s (r V)) (s (r X)) (s (t 0))) :=
    of_eq (by simp only [point, Source.Formula.rename, SyntaxAtomSyntax.zeroScalar_rename, SyntaxAtomSyntax.memberCode_rename])
      (move1 hx)
  have hw2 := of_eq (omega_rename (r w) s) (move1 hw1)
  have he := SyntaxConstructors.unique hZ2 0 0 (s (r w)) Fin.elim0 (s (t 0)) (u 0) hw2
    (.conjL hx1) (.conjL hy)
  have hc := AtomicProgramAlignment.member_symbol_subst (s (r w)) (s (t 0)) (u 0) (s (r P)) (s (r V))
    (s (r X)) he (.conjR hx1)
  exact SyntaxConstructors.unique hZ2 3 2 (s (r w)) (SyntaxAtomSyntax.three (u 0) (s (r P)) (s (r V)))
    (s (r X)) (s (r Y)) hw2 hc (.conjR hy)

/-- A freshly bound condition is bound variable zero and the same closed
carrier term is preserved in the actual lifted table. -/
theorem member_lift_fields {m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (w z D S a f c b A C K H i P V : Fin m)
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (hP : Source.Derives Γ (SyntaxVariableSyntax.code true w z P))
    (hV : Source.Derives Γ (SyntaxTermSyntax.term w z b V))
    (hi : Source.Derives Γ (.mem i f)) (hv : Source.Derives Γ (field w S i V))
    (hl : Source.Derives Γ (lifted w D S a f c b A C K H)) :
    Source.Derives Γ ((field w K z P).conj (field w H i V)) := by
  have hZero : Source.Derives Γ (((Source.Formula.mem z A).conj (field w K z P)).iff
      (SyntaxVariableSyntax.code true w z P)) := ForcingExistChildOpening.zero_fields hZ w z D S a f c b A C K H P hw hz hl
  have hClosed := InstantiateOperationFrameSyntax.intro_closedParameter w b V z hz hV
  have hFree : Source.Derives Γ (((Source.Formula.mem i f).conj (field w H i V)).iff (.equal V V)) :=
    ForcingExistChildOpening.closed_fields hZ false w D S a f c b A C K H i i V V hw hl hi hv
      HornRuleSyntax.truth_proved hClosed
  exact .conjI (.conjR (.impE (.conjR hZero) hP)) (.conjR (.impE (.conjR hFree) (.eqRefl V)))

/-- The outer or inner membership guard of the actual density compiler agrees
with the canonical guard after each path's actual binder lift. The shared
carrier is taken from the two unlifted tables. -/
private theorem compare_member_guard {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (equality inner : Bool) (R : Source.Formula (k+2))
    (w z b P V i j D S a f c A C K H D' S' a' g c' A' C' K' H' aM M Q X Y : Fin m)
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (hP : Source.Derives Γ (SyntaxVariableSyntax.code true w z P))
    (hV : Source.Derives Γ (SyntaxTermSyntax.term w z b V))
    (hi : Source.Derives Γ (numeral k i)) (hj : Source.Derives Γ (numeral (k+5) j))
    (hif : Source.Derives Γ (.mem i f)) (hjg : Source.Derives Γ (.mem j g))
    (hS : Source.Derives Γ (field w S i V)) (hS' : Source.Derives Γ (field w S' j V))
    (hLift : Source.Derives Γ (lifted w D S a f c b A C K H))
    (hLift' : Source.Derives Γ (lifted w D' S' a' g c' b A' C' K' H'))
    (hM : Source.Derives Γ (ForcingGuardCode.compiled false R w aM f P M))
    (hQ : Source.Derives Γ (OriginalTreeQuotationSyntax.tree (densityLeafTree equality R (if inner then 2 else 0)) w Q))
    (hX : Source.Derives Γ (substituted w K H A f C b M X))
    (hY : Source.Derives Γ (substituted w K' H' A' g C' b Q Y)) :
    Source.Derives Γ (.equal X Y) := by
  have hRaw := member_lift_fields hZ w z D S a f c b A C K H i P V hw hz hP hV hif hS hLift
  have hQuote := member_lift_fields hZ w z D' S' a' g c' b A' C' K' H' j P V hw hz hP hV hjg hS' hLift'
  exact member_results_eq hZ w P V X Y hw
    (ForcingRawModalBody.member_query_at hZ R w z K H A f C b P P i V aM M X hw hz hP
      (.conjL hRaw) hi (.conjR hRaw) hM hX)
    (member_of_quote hZ equality inner R w z K' H' A' g C' b j P V Q Y hw hz hj
      (.conjL hQuote) (.conjR hQuote) hQ hY)

private theorem two_below {m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (n : Nat) (i f : Fin m) (hi : Source.Derives Γ (numeral n i)) (hf : Source.Derives Γ (numeral (n+2) f)) :
    Source.Derives Γ (.mem i f) := by
  let E := (numeral (n+1) (Fin.last m)).conj (successor f.castSucc (Fin.last m))
  let Δ := Source.Context.add E (Source.Context.image Source.Formula.raise Γ)
  apply SyntaxNumeralSyntax.eliminate_succ (n+1) f _ hf
  have hE : Source.Derives Δ E := .hyp (Or.inl rfl)
  let U := (numeral n (Fin.last (m+1))).conj (successor (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Source.Context.add U (Source.Context.image Source.Formula.raise Δ)
  apply SyntaxNumeralSyntax.eliminate_succ n (Fin.last m) _ (.conjL hE)
  have hU : Source.Derives Ξ U := .hyp (Or.inl rfl)
  have hI : Source.Derives Ξ (numeral n i.castSucc.castSucc) := by
    simpa only [Source.Formula.raise, numeral_rename] using SourceLogic.under (SourceLogic.under hi E) U
  have e := SyntaxNumerals.unique (ZFContext.under (ZFContext.under hZ E) U) n
    (Fin.last (m+1)) i.castSucc.castSucc (.conjL hU) hI
  have hf1 := of_eq (successor_rename f.castSucc (Fin.last m) Fin.castSucc) (SourceLogic.under (.conjR hE) U)
  exact InsertLogic.old_member f.castSucc.castSucc (Fin.last m).castSucc (Fin.last m).castSucc i.castSucc.castSucc
    hf1 (SourceLogic.mem_subst e (InsertLogic.new_member (Fin.last m).castSucc (Fin.last (m+1))
      (Fin.last (m+1)) (.conjR hU)))

/-- Both membership leaves from the two actual density query records agree.
Read the carrier from the original table, route it into the common table,
then preserve it through each of the two actual binder lifts. -/
theorem compare_shell_members {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (k+2))
    (w z a A B f j N D b S L g S' L' i I V : Fin m)
    (v : Fin 7 → Fin m) (u t u' t' leaf' : Fin 5 → Fin m) (x y x' y' : Fin 4 → Fin m)
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (hf : Source.Derives Γ (numeral (k+2) f)) (hg : Source.Derives Γ (numeral (k+7) g))
    (hi : Source.Derives Γ (numeral k i)) (hI : Source.Derives Γ (numeral (k+5) I))
    (hv : Source.Derives Γ (field w S i V))
    (route : Source.Derives Γ (field w S i V) → Source.Derives Γ (field w S' I V))
    (hd : Source.Derives Γ (ForcingDensityCode.data R w a A B f j N D v))
    (hOuter : Source.Derives Γ (lifted w L S a f z b (u 1) (u 2) (u 3) (u 4)))
    (hInner : Source.Derives Γ (lifted w (u 3) (u 4) (u 1) f (u 2) b (t 1) (t 2) (t 3) (t 4)))
    (hOuter' : Source.Derives Γ (lifted w L' S' z g z b (u' 1) (u' 2) (u' 3) (u' 4)))
    (hInner' : Source.Derives Γ (lifted w (u' 3) (u' 4) (u' 1) g (u' 2) b (t' 1) (t' 2) (t' 3) (t' 4)))
    (hQuotes : ∀ n, Source.Derives Γ (OriginalTreeQuotationSyntax.tree (densityLeafTree equality R n) w (leaf' n)))
    (hQ : Source.Derives Γ (substituted w (u 3) (u 4) (u 1) f (u 2) b (v 2) (x 1)))
    (hR : Source.Derives Γ (substituted w (t 3) (t 4) (t 1) f (t 2) b (v 4) (y 1)))
    (hQ' : Source.Derives Γ (substituted w (u' 3) (u' 4) (u' 1) g (u' 2) b (leaf' 0) (x' 1)))
    (hR' : Source.Derives Γ (substituted w (t' 3) (t' 4) (t' 1) g (t' 2) b (leaf' 2) (y' 1))) :
    Source.Derives Γ ((Source.Formula.equal (x 1) (x' 1)).conj (.equal (y 1) (y' 1))) := by
  have hHead := Source.Derives.conjL hd
  have e := OmegaUniversal.empty_unique (v 0) z (ZFContext.arithmetic hZ).base.extensionality (.conjL hHead) hz
  have hP := SyntaxVariableImagePoint.code_subst_index true w (v 0) (v 1) z e (.conjL (.conjR hHead))
  have hif := two_below hZ k i f hi hf
  have hIg := two_below hZ (k+5) I g hI hg
  have hBase := SyntaxCodedMixedBinderTyping.input_lists w L S a f z b (u 1) (u 2) (u 3) (u 4) hOuter
  have hV := SyntaxMixedImageCodeFields.field_type w f z b S i V (.conjR hBase) hif hv
  have hv' := route hv
  have hOuterFields := member_lift_fields hZ w z L S a f z b (u 1) (u 2) (u 3) (u 4) i (v 1) V
    hw hz hP hV hif hv hOuter
  have hOuterFields' := member_lift_fields hZ w z L' S' z g z b (u' 1) (u' 2) (u' 3) (u' 4) I (v 1) V
    hw hz hP hV hIg hv' hOuter'
  refine .conjI ?_ ?_
  · exact compare_member_guard hZ equality false R w z b (v 1) V i I
      L S a f z (u 1) (u 2) (u 3) (u 4) L' S' z g z (u' 1) (u' 2) (u' 3) (u' 4)
      A (v 2) (leaf' 0) (x 1) (x' 1) hw hz hP hV hi hI hif hIg hv hv' hOuter hOuter'
      (.conjL (.conjR hd)) (hQuotes 0) hQ hQ'
  · exact compare_member_guard hZ equality true R w z b (v 1) V i I
      (u 3) (u 4) (u 1) f (u 2) (t 1) (t 2) (t 3) (t 4)
      (u' 3) (u' 4) (u' 1) g (u' 2) (t' 1) (t' 2) (t' 3) (t' 4)
      B (v 4) (leaf' 2) (y 1) (y' 1) hw hz hP hV hi hI hif hIg
      (.conjR hOuterFields) (.conjR hOuterFields') hInner hInner'
      (.conjL (.conjR (.conjR (.conjR hd)))) (hQuotes 2) hR hR'

/-- Normalize the actual outer order guard from the density compiler.
The bound head is taken from the actual lift, and the free list is that
same lift's output list. The target bound and free scopes are internal. -/
theorem outer_order_query {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (w z a A B f j N D b S L A' C K H X : Fin m)
    (v : Fin 7 → Fin m)
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (hA : Source.Derives Γ (successor A a))
    (hd : Source.Derives Γ (ForcingDensityCode.data R w a A B f j N D v))
    (hOuter : Source.Derives Γ (lifted w L S a f z b A' C K H))
    (hQ : Source.Derives Γ (substituted w K H A' f C b (v 3) X)) :
    Source.Derives Γ (ForcingGuardOpening.result true R w C f b (v 1) H
      A' (v 1) (v 3) X) := by
  have hHead := Source.Derives.conjL hd
  have e := OmegaUniversal.empty_unique (v 0) z (ZFContext.arithmetic hZ).base.extensionality (.conjL hHead) hz
  have hP := SyntaxVariableImagePoint.code_subst_index true w (v 0) (v 1) z e (.conjL (.conjR hHead))
  have hZero := ForcingExistChildOpening.zero_fields hZ w z L S a f z b A' C K H (v 1) hw hz hOuter
  have hFields := Source.Derives.impE (.conjR hZero) hP
  have hO := Source.Derives.conjL (.conjR (.conjR hd))
  have hInput := SyntaxCodedMixedBinderTyping.input_of_lifted w L S a f z b A' C K H hOuter
  have hEq := OmegaUniversal.successor_unique A A' a (ZFContext.arithmetic hZ).base.extensionality hA (.conjL (.conjR hInput))
  let P := ForcingGuardCode.compiled true R w.castSucc (Fin.last m) f.castSucc (v 1).castSucc (v 3).castSucc
  have hO' : Source.Derives Γ (ForcingGuardCode.compiled true R w A' f (v 1) (v 3)) :=
    of_eq (by simp only [P, Source.Formula.instantiate, ForcingGuardCode.compiled_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P hEq (of_eq (by simp only [P, Source.Formula.instantiate, ForcingGuardCode.compiled_rename,
        Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hO))
  exact ForcingGuardOpening.from_lifted hZ true R w z A' f C b K H (v 1) (v 3) X
    hw hz hP (.conjL hFields) (.conjR hFields) hO' hQ

private theorem lift_free_route {m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (i j src dst : Nat) (w z b L S a f A C K H L' S' a' g A' C' K' H' : Fin m)
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (hf : Source.Derives Γ (numeral src f)) (hg : Source.Derives Γ (numeral dst g))
    (hi : i < src) (hj : j < dst)
    (hRaw : Source.Derives Γ (lifted w L S a f z b A C K H))
    (hCommon : Source.Derives Γ (lifted w L' S' a' g z b A' C' K' H'))
    (hRoute : Source.Derives Γ (ForcingAtomicMonoImages.route i j w S S')) :
    Source.Derives Γ (ForcingAtomicMonoImages.route i j w H H') := by
  apply ForcingAtomicMonoImages.intro_route hZ
  intro l Δ r I J V hZ1 lift hI hJ hField
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hi1 := SyntaxNumeralMembers.index_member hZ1 src ⟨i, hi⟩ (r f) I
    (of_eq (numeral_rename src f r) (lift hf)) hI
  have hNat := SyntaxNumerals.range hZ1 i (r w) I hw1 hI
  apply eliminate_objects hZ1 1 (fun s x => (Source.Formula.mem (x 0) (s (r w))).conj (field (s (r w)) (s (r S)) (s I) (x 0)))
    (StructuralListFieldValues.exists_value hZ1 (r w) (r S) I hw1 hNat) (field (r w) (r H') J V)
  intro l' Δ' s x hZ2 move hValue
  let p := s ∘ r
  have carry {F : Source.Formula m} (h : Source.Derives Γ F) : Source.Derives Δ' (F.rename p) :=
    of_eq (SourceAlgebra.rename_comp F r s) (move (lift h))
  have hw2 := of_eq (omega_rename w p) (carry hw)
  have hz2 := of_eq (empty_rename z p) (carry hz)
  have h1 := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w L S a f z b A C K H p) (carry hRaw)
  have h2 := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w L' S' a' g z b A' C' K' H' p) (carry hCommon)
  have hBase := SyntaxCodedMixedBinderTyping.input_lists (p w) (p L) (p S) (p a) (p f) (p z) (p b)
    (p A) (p C) (p K) (p H) h1
  have hTyped := SyntaxMixedImageCodeFields.field_type (p w) (p f) (p z) (p b) (p S) (s I) (x 0)
    (.conjR hBase) (move hi1) (.conjR hValue)
  have hClosed := InstantiateOperationFrameSyntax.intro_closedParameter (p w) (p b) (x 0) (p z) hz2 hTyped
  have e := ForcingExistChildOpening.closed_fields hZ2 false (p w) (p L) (p S) (p a) (p f) (p z) (p b)
    (p A) (p C) (p K) (p H) (s I) (s I) (x 0) (s V) hw2 h1 (move hi1) (.conjR hValue)
    HornRuleSyntax.truth_proved hClosed
  have eq := Source.Derives.impE (.conjL e) (.conjI (move hi1)
    (of_eq (field_rename (r w) (r H) I V s) (move hField)))
  have hj2 := of_eq (numeral_rename j J s) (move hJ)
  have hBase' := ForcingAtomicMonoImages.use_route i j (p w) (p S) (p S') (s I) (s J) (x 0)
    (of_eq (ForcingAtomicMonoImages.route_rename i j w S S' p) (carry hRoute))
    (of_eq (numeral_rename i I s) (move hI)) hj2 (.conjR hValue)
  have hjm := SyntaxNumeralMembers.index_member hZ2 dst ⟨j, hj⟩ (p g) (s J)
    (of_eq (numeral_rename dst g p) (carry hg)) hj2
  have e' := ForcingExistChildOpening.closed_fields hZ2 false (p w) (p L') (p S') (p a') (p g) (p z) (p b)
    (p A') (p C') (p K') (p H') (s J) (s J) (x 0) (s V) hw2 h2 hjm hBase'
    HornRuleSyntax.truth_proved hClosed
  exact of_eq (field_rename (r w) (r H') J V s).symm (.conjR (.impE (.conjR e') eq))

private theorem outer_order_point {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (bound : Bool) (j : Fin (if bound then 1 else k+2))
    (w z a f a' g c b R S K H V F P x i u y o : Fin m)
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (hi : Source.Derives Γ (numeral j.val i))
    (hx : Source.Derives Γ (SyntaxVariableSyntax.code bound w i x))
    (he : Source.Derives Γ (NativeSubstitutionSyntax.environment (outerBoundMap k) (outerFreeMap k) w a f a' g R S))
    (hV : Source.Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => P) V))
    (hK : Source.Derives Γ (field w K z P))
    (hRoute : ∀ p : Fin (k+2), Source.Derives Γ (ForcingAtomicMonoImages.route p.val
      (ForcingAtomicMonoTemplate.freeIndex k .newer p).val w F H))
    (h0 : Source.Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a f a' g x u))
    (h1 : Source.Derives Γ (SyntaxCodedMixedTermSyntax.substituted w K H a' g c b u y))
    (h2 : Source.Derives Γ (SyntaxCodedMixedTermSyntax.substituted w V F a f c b x o)) :
    Source.Derives Γ (.equal y o) := by
  have hL1 := Source.Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w K H a' g c b u y h1)
  have hL2 := Source.Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w V F a f c b x o h2)
  cases bound with
  | true =>
    have hj : j.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
    have hi0 : Source.Derives Γ (empty i) := of_eq (by rw [hj] <;> rfl) hi
    have e := OmegaUniversal.empty_unique i z (ZFContext.arithmetic hZ).base.extensionality hi0 hz
    have hx0 := SyntaxVariableImagePoint.code_subst_index true w i x z e hx
    have hU := Source.Derives.conjR (.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ true w R S a f a' g x u z hw (.conjR he) hx0)) h0)
    let j0 := NativeSubstitutionImages.entryIndex (outerBoundMap k) (fo_bound_variable (0 : Fin 1))
    have hTree := Source.Derives.impE (.conjL (TermImageQuotationFields.field_at hZ _ w R j0 z u hw (.conjL (.conjL he)) hz)) hU
    have hVar := OriginalQuotationVariableFields.variable_of_tree hZ true 0 w z u hw hz
      (of_eq (by rw [NativeSubstitutionImages.get_image, outerBoundMap, ForcingRelationSource.mapping_at] <;> rfl) hTree)
    have hY := Source.Derives.conjR (.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ true w K H a' g c b u y z hw hL1 hVar)) h1)
    have hO := Source.Derives.conjR (.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ true w V F a f c b x o z hw hL2 hx0)) h2)
    have eO := Source.Derives.impE (.conjL (SyntaxForestFieldValues.field_at hZ 1 w (fun _ => P) V 0 z o hw hV hz)) hO
    have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
    exact eq_trans (StructuralListFieldValues.unique hZ w K z y P hw hzW hY hK) (eq_symm eO)
  | false =>
    let dest := ForcingAtomicMonoTemplate.freeIndex k .newer j
    have hU := Source.Derives.conjR (.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ false w R S a f a' g x u i hw (.conjR he) hx)) h0)
    have hO := Source.Derives.conjR (.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ false w V F a f c b x o i hw hL2 hx)) h2)
    let j' := NativeSubstitutionImages.entryIndex (outerFreeMap k) (fo_bound_variable j)
    have hi' : Source.Derives Γ (numeral j'.val i) := of_eq (congrArg (fun n => numeral n i)
      (ProjectNativeRenaming.variable_index (fun _ : Fin 1 => j) (fo_bound_variable 0)).symm) hi
    have hQuote := Source.Derives.impE (.conjL (TermImageQuotationFields.field_at hZ _ w S j' i u hw (.conjR (.conjL he)) hi')) hU
    have eIndex : (fo_bound_variable dest).index = dest.val :=
      ProjectNativeRenaming.variable_index (fun _ : Fin 1 => dest) (fo_bound_variable 0)
    have hTree : Source.Derives Γ (OriginalTreeQuotationSyntax.tree (.node 1 [leaf dest.val]) w u) :=
      of_eq (by
        rw [NativeSubstitutionImages.get_image, outerFreeMap, ForcingRelationSource.mapping_at]
        simp only [PureQuotationSyntax.term, PureSyntaxQuotation.termTree]
        rw [eIndex]) hQuote
    apply eliminate_objects hZ 1 (fun r p => (Source.Formula.mem (p 0) (r w)).conj (numeral dest.val (p 0)))
      (SyntaxNumerals.exists_numeral hZ dest.val w hw) (.equal y o)
    intro l Δ r p hZ1 lift hDest
    have hw1 := of_eq (omega_rename w r) (lift hw)
    have hv := OriginalQuotationVariableFields.variable_of_tree hZ1 false dest.val (r w) (p 0) (r u) hw1 (.conjR hDest)
      (of_eq (OriginalTreeQuotationSyntax.tree_rename _ w u r) (lift hTree))
    have hL := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w a' g c b K H r) (lift hL1)
    have hy := Source.Derives.conjR (.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ1 false (r w) (r K) (r H)
      (r a') (r g) (r c) (r b) (r u) (r y) (p 0) hw1 hL hv))
      (of_eq (SyntaxCodedMixedTermSyntax.substituted_rename w K H a' g c b u y r) (lift h1)))
    have ho := ForcingAtomicMonoImages.use_route j.val dest.val (r w) (r F) (r H) (r i) (p 0) (r o)
      (of_eq (ForcingAtomicMonoImages.route_rename j.val dest.val w F H r) (lift (hRoute j)))
      (of_eq (numeral_rename j.val i r) (lift hi)) (.conjR hDest) (of_eq (field_rename w F i o r) (lift hO))
    exact StructuralListFieldValues.unique hZ1 (r w) (r H) (p 0) (r y) (r o) hw1 (.conjL hDest) hy ho

private theorem outer_order_terms {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f a' g c b R S K H V F P x u y o : Fin m)
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (ha : Source.Derives Γ (numeral 1 a)) (hf : Source.Derives Γ (numeral (k+2) f))
    (he : Source.Derives Γ (NativeSubstitutionSyntax.environment (outerBoundMap k) (outerFreeMap k) w a f a' g R S))
    (hV : Source.Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => P) V))
    (hK : Source.Derives Γ (field w K z P))
    (hRoute : ∀ p : Fin (k+2), Source.Derives Γ (ForcingAtomicMonoImages.route p.val
      (ForcingAtomicMonoTemplate.freeIndex k .newer p).val w F H))
    (h0 : Source.Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a f a' g x u))
    (h1 : Source.Derives Γ (SyntaxCodedMixedTermSyntax.substituted w K H a' g c b u y))
    (h2 : Source.Derives Γ (SyntaxCodedMixedTermSyntax.substituted w V F a f c b x o)) :
    Source.Derives Γ (.equal y o) := by
  apply OriginalTermScopeElimination.eliminate w a f x (.equal y o)
    (SyntaxCodedMixedTermTyping.source_type w R S a f a' g x u h0)
  intro bound
  let n := if bound then 1 else k+2
  let lim := SyntaxTermSyntax.limit bound a f
  let E := SyntaxTermSyntax.branchWitness bound w lim x
  let Δ := Source.Context.add E (Source.Context.image Source.Formula.raise Γ)
  let r : Fin m → Fin (m+1) := Fin.castSucc
  let i := Fin.last m
  have hE : Source.Derives Δ E := .hyp (Or.inl rfl)
  have hLim : Source.Derives Γ (numeral n lim) := by cases bound <;> assumption
  have hZ1 := ZFContext.under hZ E
  have hBelow := Source.Derives.impE (.conjL (SyntaxNumeralMembers.member_iff hZ1 n (r lim) i
    (of_eq (numeral_rename n lim r) (SourceLogic.under hLim E)))) (.conjL hE)
  apply Source.Derives.impE _ hBelow
  apply SyntaxPositionSyntax.below_imp
  intro j
  apply Source.Derives.impI
  let T := numeral j.val i
  have lift {G : Source.Formula m} (h : Source.Derives Γ G) :
      Source.Derives (Source.Context.add T Δ) (G.rename r) := SourceLogic.add (SourceLogic.under h E) T
  exact outer_order_point (ZFContext.add hZ1 T) bound j (r w) (r z) (r a) (r f) (r a') (r g) (r c) (r b)
    (r R) (r S) (r K) (r H) (r V) (r F) (r P) (r x) i (r u) (r y) (r o)
    (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz)) (.hyp (Or.inl rfl)) (SourceLogic.add (.conjR hE) T)
    (of_eq (NativeSubstitutionSyntax.environment_rename (outerBoundMap k) (outerFreeMap k) w a f a' g R S r) (lift he))
    (of_eq (SyntaxForestSyntax.forest_rename 1 w (fun _ => P) V r) (lift hV))
    (of_eq (field_rename w K z P r) (lift hK))
    (fun p => of_eq (ForcingAtomicMonoImages.route_rename _ _ w F H r) (lift (hRoute p)))
    (of_eq (SyntaxCodedMixedTermSyntax.substituted_rename w R S a f a' g x u r) (lift h0))
    (of_eq (SyntaxCodedMixedTermSyntax.substituted_rename w K H a' g c b u y r) (lift h1))
    (of_eq (SyntaxCodedMixedTermSyntax.substituted_rename w V F a f c b x o r) (lift h2))

private theorem outer_order_eq {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (w z a f a' g c b K H V F P N Q X Y : Fin m)
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (ha : Source.Derives Γ (numeral 1 a)) (ha' : Source.Derives Γ (numeral 1 a'))
    (hf : Source.Derives Γ (numeral (k+2) f)) (hg : Source.Derives Γ (numeral (k+7) g))
    (hN : Source.Derives Γ (PureQuotationSyntax.formula (ForcingGuardCode.template true R) w N))
    (hQ : Source.Derives Γ (PureQuotationSyntax.formula (outerOrderLeaf R) w Q))
    (hV : Source.Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => P) V))
    (hK : Source.Derives Γ (field w K z P))
    (hRoute : ∀ p : Fin (k+2), Source.Derives Γ (ForcingAtomicMonoImages.route p.val
      (ForcingAtomicMonoTemplate.freeIndex k .newer p).val w F H))
    (hRaw : Source.Derives Γ (substituted w V F a f c b N X))
    (hCommon : Source.Derives Γ (substituted w K H a' g c b Q Y)) : Source.Derives Γ (.equal X Y) := by
  let σ : NativeSubstitutionSyntax.Mapping (fo_bound_context 1) (fo_bound_context 1) (fo_bound_context (k+7)) :=
    outerBoundMap k
  let τ : NativeSubstitutionSyntax.Mapping (fo_bound_context (k+2)) (fo_bound_context 1) (fo_bound_context (k+7)) :=
    outerFreeMap k
  have eLen (n : Nat) : (fo_bound_context n).length = n := List.length_replicate
  have hEnv := NativeSubstitutionEnvironment.exists_environment hZ σ τ w a f a' g hw
    (of_eq (congrArg (numeral · a) (eLen 1).symm) ha) (of_eq (congrArg (numeral · f) (eLen (k+2)).symm) hf)
    (of_eq (congrArg (numeral · a') (eLen 1).symm) ha') (of_eq (congrArg (numeral · g) (eLen (k+7)).symm) hg)
  apply eliminate_objects hZ 2 (fun r xs => NativeSubstitutionSyntax.environment σ τ (r w) (r a) (r f) (r a') (r g) (xs 0) (xs 1))
    hEnv (.equal X Y)
  intro l Δ r xs hZ1 lift hE
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have ha1 := of_eq (numeral_rename 1 a r) (lift ha)
  have hf1 := of_eq (numeral_rename (k+2) f r) (lift hf)
  have ht1 := of_eq (numeral_rename 1 a' r) (lift ha')
  have hg1 := of_eq (numeral_rename (k+7) g r) (lift hg)
  have hN1 := of_eq (PureQuotationSyntax.formula_rename (ForcingGuardCode.template true R) w N r) (lift hN)
  have hQ1 := of_eq (PureQuotationSyntax.formula_rename (outerOrderLeaf R) w Q r) (lift hQ)
  have hNative := NativeFormulaQuotationConstruct.construct hZ1 (ForcingGuardCode.template true R) σ τ
    (r w) (xs 0) (xs 1) (r a) (r f) (r a') (r g) (r N) (r Q) hw1
    (of_eq (congrArg (numeral · (r a)) (eLen 1).symm) ha1)
    (of_eq (congrArg (numeral · (r f)) (eLen (k+2)).symm) hf1)
    (of_eq (congrArg (numeral · (r a')) (eLen 1).symm) ht1)
    (of_eq (congrArg (numeral · (r g)) (eLen (k+7)).symm) hg1) hE hN1
    (of_eq (congrArg (fun G => PureQuotationSyntax.formula G (r w) (r Q)) (outer_order_transport R).symm) hQ1)
  apply SourceLogic.eq_symm
  apply ForcingRelationGuardFormula.compare_queries hZ1 (r w) (r a) (r f) (r a') (r g) (r c) (r b)
    (xs 0) (xs 1) (r K) (r H) (r V) (r F) (r N) (r Q) (r Y) (r X) hw1
    (SyntaxNumerals.range hZ1 1 (r w) (r a) hw1 ha1) (SyntaxNumerals.range hZ1 (k+2) (r w) (r f) hw1 hf1)
    hNative (of_eq (substituted_rename w K H a' g c b Q Y r) (lift hCommon))
    (of_eq (substituted_rename w V F a f c b N X r) (lift hRaw))
  intro l' Δ' s hZ2 move x u y o h0 h1 h2
  let p := s ∘ r
  have carry {G : Source.Formula m} (h : Source.Derives Γ G) : Source.Derives Δ' (G.rename p) :=
    of_eq (SourceAlgebra.rename_comp G r s) (move (lift h))
  exact outer_order_terms hZ2 (p w) (p z) (p a) (p f) (p a') (p g) (p c) (p b)
    (s (xs 0)) (s (xs 1)) (p K) (p H) (p V) (p F) (p P) x u y o
    (of_eq (omega_rename w p) (carry hw)) (of_eq (empty_rename z p) (carry hz))
    (of_eq (numeral_rename 1 a p) (carry ha)) (of_eq (numeral_rename (k+2) f p) (carry hf))
    (of_eq (NativeSubstitutionSyntax.environment_rename σ τ (r w) (r a) (r f) (r a') (r g) (xs 0) (xs 1) s) (move hE))
    (of_eq (SyntaxForestSyntax.forest_rename 1 w (fun _ => P) V p) (carry hV))
    (of_eq (field_rename w K z P p) (carry hK))
    (fun i => of_eq (ForcingAtomicMonoImages.route_rename _ _ w F H p) (carry (hRoute i))) h0 h1 h2

/-- The actual outer order outputs of the original density compiler and the
canonical density premise agree. The common routes come from the selected
condition table. Their validity after binder lifting is proved here. -/
theorem compare_shell_outer_order {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (k+2))
    (w z a A B f j N D b S L g S' L' Q : Fin m)
    (v : Fin 7 → Fin m) (u u' : Fin 5 → Fin m) (x x' : Fin 4 → Fin m)
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (hA : Source.Derives Γ (successor A a))
    (hf : Source.Derives Γ (numeral (k+2) f)) (hg : Source.Derives Γ (numeral (k+7) g))
    (hd : Source.Derives Γ (ForcingDensityCode.data R w a A B f j N D v))
    (hOuter : Source.Derives Γ (lifted w L S a f z b (u 1) (u 2) (u 3) (u 4)))
    (hOuter' : Source.Derives Γ (lifted w L' S' z g z b (u' 1) (u' 2) (u' 3) (u' 4)))
    (hRoute : ∀ i : Fin (k+2), Source.Derives Γ (ForcingAtomicMonoImages.route i.val
      (ForcingAtomicMonoTemplate.freeIndex k .newer i).val w S S'))
    (hQuote : Source.Derives Γ (OriginalTreeQuotationSyntax.tree (densityLeafTree equality R 1) w Q))
    (hRaw : Source.Derives Γ (substituted w (u 3) (u 4) (u 1) f (u 2) b (v 3) (x 2)))
    (hCommon : Source.Derives Γ (substituted w (u' 3) (u' 4) (u' 1) g (u' 2) b Q (x' 2))) :
    Source.Derives Γ (.equal (x 2) (x' 2)) := by
  let X := x 2
  let Y := x' 2
  let P := v 1
  let C := u 2
  let A' := u' 1
  let K := u' 3
  let F := u 4
  let H := u' 4
  have hHead := Source.Derives.conjL hd
  have e := OmegaUniversal.empty_unique (v 0) z (ZFContext.arithmetic hZ).base.extensionality (.conjL hHead) hz
  have hP := SyntaxVariableImagePoint.code_subst_index true w (v 0) P z e (.conjL (.conjR hHead))
  have hZero := ForcingExistChildOpening.zero_fields hZ w z L' S' z g z b A' (u' 2) K H P hw hz hOuter'
  have hK := Source.Derives.conjR (.impE (.conjR hZero) hP)
  have hInput := SyntaxCodedMixedBinderTyping.input_of_lifted w L S a f z b (u 1) C (u 3) F hOuter
  have hInput' := SyntaxCodedMixedBinderTyping.input_of_lifted w L' S' z g z b A' (u' 2) K H hOuter'
  have ha' : Source.Derives Γ (numeral 1 A') :=
    SyntaxNumeralSyntax.intro_succ 0 A' z hz (.conjL (.conjR hInput'))
  have ec := OmegaUniversal.successor_unique (u' 2) C z (ZFContext.arithmetic hZ).base.extensionality
    (.conjR (.conjR hInput')) (.conjR (.conjR hInput))
  have hCommon' := SyntaxMixedFormulaJudgmentSubst.subst_c w K H A' g (u' 2) b Q Y C ec hCommon
  have routes (i : Fin (k+2)) := lift_free_route hZ i.val (ForcingAtomicMonoTemplate.freeIndex k .newer i).val
    (k+2) (k+7) w z b L S a f (u 1) C (u 3) F L' S' z g A' (u' 2) K H
    hw hz hf hg i.isLt (ForcingAtomicMonoTemplate.freeIndex k .newer i).isLt hOuter hOuter' (hRoute i)
  have hDirect := outer_order_query hZ R w z a A B f j N D b S L (u 1) C (u 3) F X v hw hz hA hd hOuter hRaw
  have hQ : Source.Derives Γ (PureQuotationSyntax.formula (outerOrderLeaf R) w Q) := hQuote
  apply eliminate_objects hZ 4 (fun r ts =>
    ForcingGuardOpening.data true R (r w) (r C) (r f) (r b) (r P) (r F) (r (u 1)) (r P) (r (v 3)) (r X) ts)
    hDirect (.equal X Y)
  intro l Δ r ts hZ1 lift hd1
  have ht := Source.Derives.conjL (.conjL hd1)
  have hN := Source.Derives.conjL (.conjL (.conjR (.conjL hd1)))
  apply eliminate_objects hZ1 1 (fun s bs =>
    (SyntaxForestSyntax.forest 1 (s (r w)) (fun _ => s (r P)) (bs 0)).conj
      (substituted (s (r w)) (bs 0) (s (r F)) (s (ts 0)) (s (r f)) (s (r C)) (s (r b)) (s (ts 1)) (s (r X))))
    (.conjR hd1) (.equal (r X) (r Y))
  intro l' Δ' s bs hZ2 move hBody
  let p := s ∘ r
  have carry {G : Source.Formula m} (h : Source.Derives Γ G) : Source.Derives Δ' (G.rename p) :=
    of_eq (SourceAlgebra.rename_comp G r s) (move (lift h))
  exact outer_order_eq hZ2 R (p w) (p z) (s (ts 0)) (p f) (p A') (p g) (p C) (p b)
    (p K) (p H) (bs 0) (p F) (p P) (s (ts 1)) (p Q) (p X) (p Y)
    (of_eq (omega_rename w p) (carry hw)) (of_eq (empty_rename z p) (carry hz))
    (of_eq (numeral_rename 1 (ts 0) s) (move ht)) (of_eq (numeral_rename 1 A' p) (carry ha'))
    (of_eq (numeral_rename (k+2) f p) (carry hf)) (of_eq (numeral_rename (k+7) g p) (carry hg))
    (of_eq (PureQuotationSyntax.formula_rename (ForcingGuardCode.template true R) (r w) (ts 1) s) (move hN))
    (of_eq (PureQuotationSyntax.formula_rename (outerOrderLeaf R) w Q p) (carry hQ))
    (.conjL hBody) (of_eq (field_rename w K z P p) (carry hK))
    (fun i => of_eq (ForcingAtomicMonoImages.route_rename _ _ w F H p) (carry (routes i)))
    (.conjR hBody) (of_eq (substituted_rename w K H A' g C b Q Y p) (carry hCommon'))

end MemberGuards

private def layoutTail {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) :
    Fin 5 → PureSyntaxQuotation.Fm [] (fo_bound_context (k+7)) :=
  let head := layoutHead equality R
  let endForm := head 4
  let fourth := (head 3).imp endForm
  let third := (head 2).imp fourth
  let second := (head 1).imp third
  Fin.cases (layoutFormula equality R) (Fin.cases second (Fin.cases third (Fin.cases fourth (fun _ => endForm))))

private theorem layout_tail_imp {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) (i : Fin 4) :
    layoutTail equality R i.castSucc = .imp (layoutHead equality R i.castSucc) (layoutTail equality R i.succ) := by
  refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i

-- Matching quotation and proof interfaces only needs the named predicates.
attribute [local irreducible] ForcingAtomicRelations.forces ForcingAtomicBasic.preorder
  NaturalRecursionSyntax.matrix OriginalAxiomCodeTest.test
  InternalProofBackground.implication SyntaxMixedFormulaJudgmentSyntax.substituted FormulaCodeSyntax.formulaCode

set_option maxHeartbeats 400000 in
/-- Assemble the original implications from the actual five leaf queries in
one environment, using the actual atomic output F as the terminal code. -/
theorem from_queries {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (k+2))
    (w z g b B L Extra Pre D F : Fin m) (H layout : Fin 6 → Fin m) (N : Fin 5 → Fin m)
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (hg : Source.Derives Γ (numeral (k+7) g))
    (hm : Source.Derives Γ (SyntaxMixedImageCodeSyntax.termLists w z g z b B L))
    (hQuote : ∀ i, Source.Derives Γ (PureQuotationSyntax.formula (layoutHead equality R i) w (N i)))
    (hRun : ∀ i, Source.Derives Γ (substituted w B L z g z b (N i)
      (Fin.lastCases F (ForcingAtomicMono.heads Pre D H) i)))
    (hExtra : Source.Derives Γ (FormulaCodeSyntax.formulaCode w Extra z b))
    (hLayout : Source.Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (hDense : Source.Derives Γ (implication test w z b (layout 3) D)) :
    Source.Derives Γ (implication test w z b (layout 3) F) := by
  let out := implication test w z b (layout 3) F
  let head := ForcingAtomicMono.heads Pre D H
  let trees := fun i : Fin 4 => PureSyntaxQuotation.formulaTree (layoutTail equality R i.castSucc)
  apply ProjectCompilerQuotation.eliminate_quotations hZ 4 trees w hw out
  intro l Δ r qs hZ1 lift hTrees
  let tCode : Fin 5 → Fin l := Fin.lastCases (r (N 4)) qs
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  have hg1 := of_eq (numeral_rename (k+7) g r) (lift hg)
  have hm1 := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w z g z b B L r) (lift hm)
  have hLeaf (i : Fin 5) : Source.Derives Δ (PureQuotationSyntax.formula
      (layoutHead equality R i) (r w) (r (N i))) :=
    of_eq (PureQuotationSyntax.formula_rename (layoutHead equality R i) w (N i) r) (lift (hQuote i))
  have hTail (i : Fin 5) : Source.Derives Δ (PureQuotationSyntax.formula
      (layoutTail equality R i) (r w) (tCode i)) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [tCode, Fin.lastCases_last]
      change Source.Derives Δ (PureQuotationSyntax.formula (layoutHead equality R 4) (r w) (r (N 4)))
      exact hLeaf 4
    · simp only [tCode, Fin.lastCases_castSucc]
      exact hTrees j
  have hRuns (i : Fin 5) : Source.Derives Δ (substituted (r w) (r B) (r L) (r z) (r g)
      (r z) (r b) (r (N i)) (r (Fin.lastCases F head i))) :=
    of_eq (substituted_rename w B L z g z b (N i) (Fin.lastCases F head i) r) (lift (hRun i))
  have hCtor (i : Fin 4) : Source.Derives Δ (SyntaxLogicalSyntax.binaryCode 2 (r w) (r (N i.castSucc))
      (tCode i.succ) (tCode i.castSucc)) := by
    let X := layoutHead equality R i.castSucc
    let Y := layoutTail equality R i.succ
    have hNode := of_eq (congrArg (fun p => PureQuotationSyntax.formula p (r w) (tCode i.castSucc))
      (layout_tail_imp equality R i)) (hTail i.castSucc)
    exact OriginalQuotationNodeFields.tree_to_constructor hZ1 7
      [PureSyntaxQuotation.formulaTree X, PureSyntaxQuotation.formulaTree Y]
      (r w) (tCode i.castSucc) (SyntaxAtomSyntax.two (r (N i.castSucc)) (tCode i.succ)) hw1
      (.conjI (hLeaf i.castSucc) (.conjI (hTail i.succ) (.eqRefl (r w)))) hNode
  have hInput (i : Fin 4) : Source.Derives Δ (SyntaxMixedFormulaOutputSyntax.input
      (r w) (r B) (r L) (r z) (r g) (r z) (r b) (tCode i.castSucc)) :=
    .conjI (PureQuotationFormulaTyping.formula_type hZ1 (layoutTail equality R i.castSucc)
      (r w) (r z) (r g) (tCode i.castSucc) hw1 hz1
      (of_eq (by rw [List.length_replicate]) hg1) (hTail i.castSucc)) hm1
  apply of_eq (implication_rename test w z b (layout 3) F r).symm
  apply ForcingAtomicMonoImages.with_chain hZ1 (r w) (r z) (r g) (r b) (r B) (r L) (r F) 4
    (fun i => r (N i.castSucc)) (fun i => r (head i)) tCode hw1 hInput hCtor
    (fun i => by simpa only [Fin.lastCases_castSucc] using hRuns i.castSucc)
    (by
      simp only [tCode, Fin.lastCases_last]
      have hLast : Fin.last 4 = (4 : Fin 5) := Fin.ext rfl
      have ht := hRuns (Fin.last 4)
      rw [Fin.lastCases_last, hLast] at ht
      exact ht)
    (implication test (r w) (r z) (r b) (r (layout 3)) (r F))
  intro l2 Δ2 s values hZ2 move hLast hNodes hMix
  let ρ := fun i => s (r i)
  have carry {φ : Source.Formula m} (h : Source.Derives Γ φ) : Source.Derives Δ2 (φ.rename ρ) :=
    of_eq (rename_comp φ r s) (move (lift h))
  have hFull : Source.Derives Δ (PureQuotationSyntax.formula (layoutFormula equality R) (r w) (tCode 0)) := hTail 0
  have result := at_instance hZ2 equality R (ρ w) (ρ z) (ρ g) (ρ b) (ρ B) (ρ L)
    (s (tCode 0)) (ρ Extra) (ρ Pre) (ρ D) (fun i => ρ (H i)) (fun i => ρ (layout i)) values
    (of_eq (omega_rename w ρ) (carry hw)) (of_eq (empty_rename z ρ) (carry hz))
    (of_eq (numeral_rename (k+7) g ρ) (carry hg))
    (of_eq (PureQuotationSyntax.formula_rename (layoutFormula equality R) (r w) (tCode 0) s) (move hFull))
    hMix (fun i => of_eq (by refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) i) (hNodes i))
    (of_eq (FormulaCodeSyntax.formulaCode_rename w Extra z b ρ) (carry hExtra))
    (of_eq (ForcingProofContext.layoutData_rename w z b Extra Pre H layout ρ) (carry hLayout))
    (of_eq (implication_rename test w z b (layout 3) D ρ) (carry hDense))
  exact of_eq (implication_rename test (r w) (r z) (r b) (r (layout 3)) (r F) s).symm
    (of_eq (congrArg (implication test (ρ w) (ρ z) (ρ b) (ρ (layout 3))) hLast) result)

private theorem with_density_query {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (k+2)) (w z g b B L : Fin m)
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (hg : Source.Derives Γ (numeral (k+7) g))
    (hm : Source.Derives Γ (SyntaxMixedImageCodeSyntax.termLists w z g z b B L))
    (out : Source.Formula m)
    (use : ∀ {l} {Δ : Source.Context l} (r : Fin m → Fin l) (N D : Fin l), ZFContext.Evidence Δ →
      (∀ {φ : Source.Formula m}, Source.Derives Γ φ → Source.Derives Δ (φ.rename r)) →
      Source.Derives Δ (PureQuotationSyntax.formula (layoutHead equality R 3) (r w) N) →
      Source.Derives Δ (substituted (r w) (r B) (r L) (r z) (r g) (r z) (r b) N D) →
      Source.Derives Δ (out.rename r)) : Source.Derives Γ out := by
  let F := layoutHead equality R 3
  have he := PureQuotationTypedFormulas.exists_typed hZ F w z g hw hz
    (of_eq (by rw [List.length_replicate]) hg)
  apply NativeProofQuotation.eliminate_objects hZ 1
    (fun r xs => PureQuotationTypedSyntax.formulaValue F (r w) (r z) (r g) (xs 0)) he out
  intro l Δ r qs hZ1 lift hValue
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hm1 := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w z g z b B L r) (lift hm)
  have hN : Source.Derives Δ (PureQuotationSyntax.formula F (r w) (qs 0)) := .conjL hValue
  have hRun := SyntaxMixedFormulaOutputInduction.actual_exists hZ1
    (r w) (r B) (r L) (r z) (r g) (r z) (r b) (qs 0) hw1 (.conjI (.conjR hValue) hm1)
  apply NativeProofQuotation.eliminate_objects hZ1 1 (fun s ds =>
    substituted (s (r w)) (s (r B)) (s (r L)) (s (r z)) (s (r g)) (s (r z)) (s (r b))
      (s (qs 0)) (ds 0)) hRun (out.rename r)
  intro l2 Δ2 s ds hZ2 move hD
  let ρ := fun i => s (r i)
  have carry {φ : Source.Formula m} (h : Source.Derives Γ φ) : Source.Derives Δ2 (φ.rename ρ) :=
    of_eq (rename_comp φ r s) (move (lift h))
  exact of_eq (rename_comp out r s).symm
    (use ρ (s (qs 0)) (ds 0) hZ2 carry
      (of_eq (PureQuotationSyntax.formula_rename F (r w) (qs 0) s) (move hN)) hD)

def densityStepData {k m : Nat} (equality : Bool) (R : Source.Formula (k+2))
    (w z g b B L G F N D : Fin m) : Source.Formula m :=
  (PureQuotationSyntax.formula (layoutHead equality R 3) w N).conj
    ((substituted w B L z g z b N D).conj ((implication test w z b G D).imp (implication test w z b G F)))

theorem densityStepData_rename {k m l : Nat} (equality : Bool) (R : Source.Formula (k+2))
    (w z g b B L G F N D : Fin m) (r : Fin m → Fin l) :
    (densityStepData equality R w z g b B L G F N D).rename r =
      densityStepData equality R (r w) (r z) (r g) (r b) (r B) (r L) (r G) (r F) (r N) (r D) := by
  simp only [densityStepData, Source.Formula.rename, PureQuotationSyntax.formula_rename,
    substituted_rename, implication_rename]

/-- The same actual density code produced by the compiler is the antecedent
of the internal proof transfer. -/
def densityStep {k m : Nat} (equality : Bool) (R : Source.Formula (k+2)) (w z g b B L G F : Fin m) :
    Source.Formula m := existsMany 2
  (densityStepData equality R (old 2 w) (old 2 z) (old 2 g) (old 2 b) (old 2 B) (old 2 L)
    (old 2 G) (old 2 F) (slot 2 0) (slot 2 1))

theorem densityStep_rename {k m l : Nat} (equality : Bool) (R : Source.Formula (k+2))
    (w z g b B L G F : Fin m) (r : Fin m → Fin l) :
    (densityStep equality R w z g b B L G F).rename r =
      densityStep equality R (r w) (r z) (r g) (r b) (r B) (r L) (r G) (r F) := by
  simp only [densityStep, existsMany_rename, densityStepData_rename, lift_old, lift_slot]

def existingLeaf : Fin 4 → Fin 5 :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (fun _ => 4)))

set_option maxHeartbeats 400000 in
/-- Generate the density query from the actual common table. The four other
queries retain their original preorder, membership, order and atomic outputs. -/
theorem from_common_table {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (k+2))
    (w z g b B L Extra Pre F : Fin m) (H layout : Fin 6 → Fin m) (N : Fin 4 → Fin m)
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (hg : Source.Derives Γ (numeral (k+7) g))
    (hm : Source.Derives Γ (SyntaxMixedImageCodeSyntax.termLists w z g z b B L))
    (hQuote : ∀ i, Source.Derives Γ (PureQuotationSyntax.formula (layoutHead equality R (existingLeaf i)) w (N i)))
    (hRun : ∀ i, Source.Derives Γ (substituted w B L z g z b (N i)
      (Fin.cases Pre (Fin.cases (H 1) (Fin.cases (H 4) (fun _ => F))) i)))
    (hExtra : Source.Derives Γ (FormulaCodeSyntax.formulaCode w Extra z b))
    (hLayout : Source.Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout)) :
    Source.Derives Γ (densityStep equality R w z g b B L (layout 3) F) := by
  let out := densityStep equality R w z g b B L (layout 3) F
  apply with_density_query hZ equality R w z g b B L hw hz hg hm out
  intro l Δ r n d hZ1 lift hN hD
  let codes : Fin 5 → Fin l :=
    Fin.cases (r (N 0)) (Fin.cases (r (N 1)) (Fin.cases (r (N 2)) (Fin.cases n (fun _ => r (N 3)))))
  have q (i : Fin 4) := of_eq (PureQuotationSyntax.formula_rename
    (layoutHead equality R (existingLeaf i)) w (N i) r) (lift (hQuote i))
  have run (i : Fin 4) := of_eq (substituted_rename w B L z g z b (N i)
    (Fin.cases Pre (Fin.cases (H 1) (Fin.cases (H 4) (fun _ => F))) i) r) (lift (hRun i))
  have hQuotes : ∀ i, Source.Derives Δ (PureQuotationSyntax.formula (layoutHead equality R i) (r w) (codes i)) :=
    Fin.cases (q 0) (Fin.cases (q 1) (Fin.cases (q 2) (Fin.cases hN (fun _ => q 3))))
  have hRuns : ∀ i, Source.Derives Δ (substituted (r w) (r B) (r L) (r z) (r g) (r z) (r b)
      (codes i) (Fin.lastCases (r F) (ForcingAtomicMono.heads (r Pre) d (fun j => r (H j))) i)) := by
    intro i
    refine Fin.cases (run 0) (Fin.cases (run 1) (Fin.cases (run 2) (Fin.cases hD (fun j => ?_)))) i
    have he : j = 0 := Subsingleton.elim _ _
    subst j
    exact run 3
  let E := implication test (r w) (r z) (r b) (r (layout 3)) d
  have hTransfer : Source.Derives Δ (E.imp (implication test (r w) (r z) (r b) (r (layout 3)) (r F))) := by
    apply Source.Derives.impI
    exact from_queries (ZFContext.add hZ1 E) equality R (r w) (r z) (r g) (r b) (r B) (r L)
      (r Extra) (r Pre) d (r F) (fun j => r (H j)) (fun j => r (layout j)) codes
      (SourceLogic.add (of_eq (omega_rename w r) (lift hw)) E) (SourceLogic.add (of_eq (empty_rename z r) (lift hz)) E)
      (SourceLogic.add (of_eq (numeral_rename (k+7) g r) (lift hg)) E)
      (SourceLogic.add (of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w z g z b B L r) (lift hm)) E)
      (fun i => SourceLogic.add (hQuotes i) E) (fun i => SourceLogic.add (hRuns i) E)
      (SourceLogic.add (of_eq (FormulaCodeSyntax.formulaCode_rename w Extra z b r) (lift hExtra)) E)
      (SourceLogic.add (of_eq (ForcingProofContext.layoutData_rename w z b Extra Pre H layout r) (lift hLayout)) E)
      (.hyp (Or.inl rfl))
  apply of_eq (densityStep_rename equality R w z g b B L (layout 3) F r).symm
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two n d)
  exact of_eq (by simp only [densityStepData_rename, assign_old, assign_slot]; rfl)
    (.conjI hN (.conjI hD hTransfer) : Source.Derives Δ
      (densityStepData equality R (r w) (r z) (r g) (r b) (r B) (r L) (r (layout 3)) (r F) n d))

def canonicalStep {k m : Nat} (equality : Bool) (R : Source.Formula (k+2)) (w z b B G F : Fin m) :
    Source.Formula m := existsMany 2
  (densityStep equality R (old 2 w) (old 2 z) (slot 2 0) (old 2 b) (old 2 B) (slot 2 1) (old 2 G) (old 2 F))

theorem canonicalStep_rename {k m l : Nat} (equality : Bool) (R : Source.Formula (k+2))
    (w z b B G F : Fin m) (r : Fin m → Fin l) :
    (canonicalStep equality R w z b B G F).rename r =
      canonicalStep equality R (r w) (r z) (r b) (r B) (r G) (r F) := by
  simp only [canonicalStep, existsMany_rename, densityStep_rename, lift_old, lift_slot]

private theorem head_agreement {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) (i : Fin 4) :
    layoutHead equality R (existingLeaf i) =
      ForcingAtomicMonoTemplate.nativeLeaf equality R (ForcingAtomicMonoTemplate.partAt (existingLeaf i)) := by
  refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) i

/-- Start from the original preorder and compiler queries, before any of them
has been run on the common table. Both the common table and the density
output are produced internally. -/
theorem from_canonical_fields {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Source.Formula (k+2))
    (w z f J b B S A3 D3 t0 t1 D0 D1 S0 S1 x y p q c Extra Pre Fp Fq : Fin m)
    (H layout : Fin 6 → Fin m) (N : Fin 5 → Fin m)
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (hf : Source.Derives Γ (numeral (k+2) f)) (hJ : Source.Derives Γ (numeral (k+1) J))
    (hA : Source.Derives Γ (numeral 3 A3)) (ht0 : Source.Derives Γ (numeral 2 t0)) (ht1 : Source.Derives Γ (numeral 2 t1))
    (hTerms : ∀ v, v ∈ [y,x,q,c,p] → Source.Derives Γ (SyntaxTermSyntax.term w z b v))
    (hD3 : Source.Derives Γ (SyntaxForestSyntax.forest 3 w (Source.SetLanguage.args3 p q c) D3))
    (hD0 : Source.Derives Γ (SyntaxForestSyntax.forest 2 w (Source.SetLanguage.args2 y x) D0))
    (hD1 : Source.Derives Γ (SyntaxForestSyntax.forest 2 w (Source.SetLanguage.args2 y x) D1))
    (hS0 : Source.Derives Γ (ForcingReflexiveImages.replacement w f z b S J p S0))
    (hS1 : Source.Derives Γ (ForcingReflexiveImages.replacement w f z b S J q S1))
    (hQuotes : ∀ i, Source.Derives Γ (PureQuotationSyntax.formula
      (ForcingAtomicMonoTemplate.leaf equality R (ForcingAtomicMonoTemplate.partAt i)) w (N i)))
    (hPre : Source.Derives Γ (substituted w B S z f z b (N 0) Pre))
    (hMem : Source.Derives Γ (substituted w D3 S A3 f z b (N 1) (H 1)))
    (hOrd : Source.Derives Γ (substituted w D3 S A3 f z b (N 2) (H 4)))
    (hOld : Source.Derives Γ (substituted w D0 S0 t0 f z b (N 3) Fp))
    (hNew : Source.Derives Γ (substituted w D1 S1 t1 f z b (N 4) Fq))
    (hExtra : Source.Derives Γ (FormulaCodeSyntax.formulaCode w Extra z b))
    (hLayout : Source.Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout)) :
    Source.Derives Γ (canonicalStep equality R w z b B (layout 3) Fq) := by
  let out := canonicalStep equality R w z b B (layout 3) Fq
  apply ForcingAtomicMonoImages.with_aligned_queries hZ equality R
    w z f J b B S A3 D3 t0 t1 D0 D1 S0 S1 x y p q c Pre Fp Fq H N
    hw hz hf hJ hA ht0 ht1 hTerms hD3 hD0 hD1 hS0 hS1 hQuotes hPre hMem hOrd hOld hNew out
  intro l Δ r g L Q hZ1 lift hg hm hQuote hRun _
  have hQuoted (i : Fin 4) : Source.Derives Δ (PureQuotationSyntax.formula
      (layoutHead equality R (existingLeaf i)) (r w) (Q (existingLeaf i))) :=
    of_eq (congrArg (fun F => PureQuotationSyntax.formula F (r w) (Q (existingLeaf i)))
      (head_agreement equality R i).symm) (hQuote (existingLeaf i))
  have hQueries (i : Fin 4) : Source.Derives Δ (substituted (r w) (r B) L (r z) g (r z) (r b)
      (Q (existingLeaf i)) (Fin.cases (r Pre) (Fin.cases (r (H 1)) (Fin.cases (r (H 4)) (fun _ => r Fq))) i)) := by
    refine Fin.cases (hRun 0) (Fin.cases (hRun 1) (Fin.cases (hRun 2) (fun _ => hRun 4))) i
  have result := from_common_table hZ1 equality R (r w) (r z) g (r b) (r B) L (r Extra) (r Pre) (r Fq)
    (fun i => r (H i)) (fun i => r (layout i)) (fun i => Q (existingLeaf i))
    (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz)) hg hm hQuoted hQueries
    (of_eq (FormulaCodeSyntax.formulaCode_rename w Extra z b r) (lift hExtra))
    (of_eq (ForcingProofContext.layoutData_rename w z b Extra Pre H layout r) (lift hLayout))
  apply of_eq (canonicalStep_rename equality R w z b B (layout 3) Fq r).symm
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two g L)
  exact of_eq (by simp only [densityStep_rename, assign_old, assign_slot]; rfl) result

/-- Read the original atomic compiler and both actual condition queries.
The argument image lists, the original preorder fields and the density code
are all obtained by the existing object constructors. -/
theorem from_runtime {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Source.Formula (k+2))
    (w z a f j b B R S T S0 S1 A1 A2 A3 K Extra X Y A Fp Fq : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m)
    (hr : Source.Derives Γ (ForcingRawModalBody.globalModalInput test Reln w z a f j b B R S T S0 S1 A1 A2 A3 K Extra
      raw v C Refl Pre U0 P rows layout))
    (hw : Source.Derives Γ (omega w)) (hz : Source.Derives Γ (empty z))
    (hf : Source.Derives Γ (numeral (k+2) f))
    (hX : Source.Derives Γ (SyntaxTermSyntax.term w a z X)) (hY : Source.Derives Γ (SyntaxTermSyntax.term w a z Y))
    (hAtom : Source.Derives Γ (ForcingAtomicCode.compiled equality Reln w a X Y A))
    (hOld : Source.Derives Γ (substituted w T S0 a f z b A Fp))
    (hNew : Source.Derives Γ (substituted w T S1 a f z b A Fq)) :
    Source.Derives Γ (canonicalStep equality Reln w z b R (layout 3) Fq) := by
  let out := canonicalStep equality Reln w z b R (layout 3) Fq
  apply ForcingAtomicMonoImages.with_runtime_fields hZ equality Reln
    w z a f j b B R S T S0 S1 A1 A2 A3 K Extra X Y A Fp Fq raw v C Refl Pre U0 P rows layout
    hr hw hz hf hX hY hAtom hOld hNew out
  intro l Δ r hZ1 _
  intro f' J S' A3' D3 t0 t1 D0 D1 S0' S1' x y p q c Extra' Pre' H N
    hw1 hz1 hf1 hJ hA ht0 ht1 hTerms hD3 hD0 hD1 hS0 hS1 hQuotes hPre hMem hOrd hOld1 hNew1 hExtra hLayout
  exact of_eq (canonicalStep_rename equality Reln w z b R (layout 3) Fq r).symm
    (from_canonical_fields hZ1 equality Reln
      (r w) (r z) f' J (r b) (r R) S' A3' D3 t0 t1 D0 D1 S0' S1' x y p q c Extra' Pre' (r Fp) (r Fq)
      H (fun i => r (layout i)) N hw1 hz1 hf1 hJ hA ht0 ht1 hTerms hD3 hD0 hD1 hS0 hS1 hQuotes
      hPre hMem hOrd hOld1 hNew1 hExtra hLayout)

private theorem typed_at_free_scope {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Source.Formula (k+2)) (w a f X Y A : Fin m)
    (hf : Source.Derives Γ (numeral (k+2) f))
    (hAtom : Source.Derives Γ (ForcingAtomicCode.compiled equality Reln w a X Y A)) :
    Source.Derives Γ (FormulaCodeSyntax.formulaCode w A a f) := by
  let out := FormulaCodeSyntax.formulaCode w A a f
  apply NativeProofQuotation.eliminate_objects hZ 1 (fun r xs =>
    (numeral (k+2) (xs 0)).conj (FormulaCodeSyntax.formulaCode (r w) (r A) (r a) (xs 0)))
    (ForcingAtomicCode.compiled_type equality Reln w a X Y A hAtom) out
  intro l Δ r xs hZ1 lift ht
  have he := SyntaxNumerals.unique hZ1 (k+2) (xs 0) (r f) (.conjL ht)
    (of_eq (numeral_rename (k+2) f r) (lift hf))
  let E := FormulaCodeSyntax.formulaCode (r w).castSucc (r A).castSucc (r a).castSucc (Fin.last l)
  have hCode : Source.Derives Δ (FormulaCodeSyntax.formulaCode (r w) (r A) (r a) (r f)) :=
    of_eq (by simp only [E, Source.Formula.instantiate, FormulaCodeSyntax.formulaCode_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Source.Derives.eqSubst E he
        (of_eq (by simp only [E, Source.Formula.instantiate, FormulaCodeSyntax.formulaCode_rename,
          Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR ht)))
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w A a f r).symm hCode

/-- At the actual current condition query, produce and eliminate the older
condition query with the original typed compiler and overwrite table. -/
theorem from_new_query {k m : Nat} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Source.Formula (k+2))
    (w z a f j b B R S T S0 S1 A1 A2 A3 K Extra X Y A Fq : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m)
    (hr : Source.Derives Γ (ForcingRawModalBody.globalModalInput test Reln w z a f j b B R S T S0 S1 A1 A2 A3 K Extra
      raw v C Refl Pre U0 P rows layout))
    (hX : Source.Derives Γ (SyntaxTermSyntax.term w a z X)) (hY : Source.Derives Γ (SyntaxTermSyntax.term w a z Y))
    (hAtom : Source.Derives Γ (ForcingAtomicCode.compiled equality Reln w a X Y A))
    (hNew : Source.Derives Γ (substituted w T S1 a f z b A Fq)) :
    Source.Derives Γ (canonicalStep equality Reln w z b R (layout 3) Fq) := by
  let out := canonicalStep equality Reln w z b R (layout 3) Fq
  have hGlobal := Source.Derives.conjL hr
  have hFresh := Source.Derives.conjL (.conjL (.conjR hGlobal))
  have hBasis := Source.Derives.conjL (.conjL (.conjL hGlobal))
  have hw : Source.Derives Γ (omega w) := .conjL (.conjL (.conjL (.conjR (.conjR hFresh))))
  have hz : Source.Derives Γ (empty z) := .conjL hFresh
  have hf : Source.Derives Γ (numeral (k+2) f) := .conjL (.conjR (.conjR (.conjR (.conjR hBasis))))
  have hAux := Source.Derives.conjR hr
  have hT : Source.Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z b T) := .conjL hAux
  have hRep : Source.Derives Γ (ForcingReflexiveImages.replacement w f z b S j (P 0 2) S0) :=
    .conjL (.conjR (.conjR hAux))
  have hS := ForcingReflexiveImages.target_type w f z b S j (P 0 2) S0 hRep
  have ht := typed_at_free_scope hZ equality Reln w a f X Y A hf hAtom
  have he := SyntaxMixedFormulaOutputInduction.actual_exists hZ w T S0 a f z b A hw
    (.conjI ht (.conjI hT hS))
  apply NativeProofQuotation.eliminate_objects hZ 1 (fun r xs =>
    substituted (r w) (r T) (r S0) (r a) (r f) (r z) (r b) (r A) (xs 0)) he out
  intro l Δ r xs hZ1 lift hOld
  have hr1 := of_eq (ForcingRawModalBody.globalModalInput_rename test Reln w z a f j b B R S T S0 S1
    A1 A2 A3 K Extra raw v C Refl Pre U0 P rows layout r) (lift hr)
  apply of_eq (canonicalStep_rename equality Reln w z b R (layout 3) Fq r).symm
  exact from_runtime hZ1 equality Reln (r w) (r z) (r a) (r f) (r j) (r b) (r B) (r R) (r S)
    (r T) (r S0) (r S1) (r A1) (r A2) (r A3) (r K) (r Extra) (r X) (r Y) (r A) (xs 0) (r Fq)
    (fun i => r (raw i)) (fun i => r (v i)) (fun i => r (C i)) (fun i => r (Refl i))
    (fun i => r (Pre i)) (fun i => r (U0 i)) (fun i j => r (P i j)) (fun i => r (rows i)) (fun i => r (layout i)) hr1
    (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz))
    (of_eq (numeral_rename (k+2) f r) (lift hf))
    (of_eq (SyntaxTermSyntax.term_rename w a z X r) (lift hX)) (of_eq (SyntaxTermSyntax.term_rename w a z Y r) (lift hY))
    (of_eq (ForcingAtomicCode.compiled_rename equality Reln w a X Y A r) (lift hAtom))
    hOld (of_eq (substituted_rename w T S1 a f z b A Fq r) (lift hNew))

def runtimeInput {k m : Nat} (equality : Bool) (Reln : Source.Formula (k+2))
    (w z a f j b B R S T S0 S1 A1 A2 A3 K Extra X Y A Fq : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) : Source.Formula m :=
  (ForcingRawModalBody.globalModalInput test Reln w z a f j b B R S T S0 S1 A1 A2 A3 K Extra
    raw v C Refl Pre U0 P rows layout).conj
    ((SyntaxTermSyntax.term w a z X).conj ((SyntaxTermSyntax.term w a z Y).conj
      ((ForcingAtomicCode.compiled equality Reln w a X Y A).conj (substituted w T S1 a f z b A Fq))))

def sentence {k m : Nat} (equality : Bool) (Reln : Source.Formula (k+2))
    (w z a f j b B R S T S0 S1 A1 A2 A3 K Extra X Y A Fq : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) : Source.Sentence :=
  ((runtimeInput equality Reln w z a f j b B R S T S0 S1 A1 A2 A3 K Extra X Y A Fq raw v C Refl Pre U0 P rows layout).imp
    (canonicalStep equality Reln w z b R (layout 3) Fq)).close

theorem kernel_certificate {k m : Nat} (equality : Bool) (Reln : Source.Formula (k+2))
    (w z a f j b B R S T S0 S1 A1 A2 A3 K Extra X Y A Fq : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) :
    FirstOrder.Derives nativeZF [] (Translation.sentence
      (sentence equality Reln w z a f j b B R S T S0 S1 A1 A2 A3 K Extra X Y A Fq raw v C Refl Pre U0 P rows layout)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Source.Derives.impI
  let I := runtimeInput equality Reln w z a f j b B R S T S0 S1 A1 A2 A3 K Extra X Y A Fq raw v C Refl Pre U0 P rows layout
  have h : Source.Derives (Source.Context.add I (Source.SetLanguage.ZF.at m)) I := .hyp (Or.inl rfl)
  exact from_new_query (ZFContext.add (ZFContext.source_ZF m) I) equality Reln
    w z a f j b B R S T S0 S1 A1 A2 A3 K Extra X Y A Fq raw v C Refl Pre U0 P rows layout
    (.conjL h) (.conjL (.conjR h)) (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h)))) (.conjR (.conjR (.conjR (.conjR h))))

end PPAC.Migration.ForcingAtomicDenseTemplate
