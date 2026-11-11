import PPAC.Migration.ForcingPreorderCode
import PPAC.Migration.ForcingRelationSource
import PPAC.Migration.NativeProofQuotation

/-! Put the actual atomic compiler and preorder leaves in one native free
context. The five leading slots are y, x, q, r, p. The remainder is the
unchanged shared free table, including its original condition slot. -/
namespace PPAC.Migration.ForcingAtomicMonoTemplate
open Internal Source SourceAlgebra
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open SetTheory.Definitional.Project (fo_bound_context fo_bound_variable)
attribute [local implicit_reducible] SetTheory.signature
attribute [local implicit_reducible] Definitional.Project.FirstOrderSemantics.reduct
set_option maxRecDepth 32768

inductive Part
  | preorder | member | order | older | newer

abbrev depth : Part → Nat
  | .preorder => 0
  | .member | .order => 3
  | .older | .newer => 2

def base {k : Nat} (i : Fin (k+2)) : Fin (k+7) := i.addNat 5

def params {k : Nat} (i : Fin k) : Fin (k+7) := base i.castSucc.castSucc

def carrier (k : Nat) : Fin (k+7) := base (Fin.last k).castSucc

def boundIndex (k : Nat) : (part : Part) → Fin (depth part) → Fin (k+7)
  | .preorder => Fin.elim0
  | .member | .order => Fin.cases 4 (Fin.cases 2 (fun _ => 3))
  | .older | .newer => Fin.cases 0 (fun _ => 1)

def freeIndex (k : Nat) : Part → Fin (k+2) → Fin (k+7)
  | .older => Fin.lastCases 4 (fun i => base i.castSucc)
  | .newer => Fin.lastCases 2 (fun i => base i.castSucc)
  | _ => base

private def atomBoundMap (k : Nat) :
    NativeSubstitutionSyntax.Mapping (fo_bound_context 2) [] (fo_bound_context (k+7)) :=
  ForcingRelationSource.mapping (fun i => .fvar (fo_bound_variable (boundIndex k .older i)))

def boundMap (k : Nat) : (part : Part) →
    NativeSubstitutionSyntax.Mapping (fo_bound_context (depth part)) [] (fo_bound_context (k+7))
  | .preorder => ForcingRelationSource.emptyMap
  | .member => ForcingRelationSource.mapping (fun i => .fvar (fo_bound_variable (boundIndex k .member i)))
  | .order => ForcingRelationSource.mapping (fun i => .fvar (fo_bound_variable (boundIndex k .order i)))
  | .older | .newer => atomBoundMap k

def freeMap (k : Nat) (part : Part) :
    NativeSubstitutionSyntax.Mapping (fo_bound_context (k+2)) [] (fo_bound_context (k+7)) :=
  ForcingRelationSource.mapping (fun i => .fvar (fo_bound_variable (freeIndex k part i)))

theorem bound_map_at (k : Nat) (part : Part) (i : Fin (depth part)) :
    boundMap k part (fo_bound_variable i) = .fvar (fo_bound_variable (boundIndex k part i)) := by
  cases part with
  | preorder => exact Fin.elim0 i
  | member | order | older | newer =>
    simp only [boundMap, atomBoundMap, ForcingRelationSource.mapping_at] <;> rfl

def leaf {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) :
    (part : Part) → PureSyntaxQuotation.Fm (fo_bound_context (depth part)) (fo_bound_context (k+2))
  | .preorder => ForcingPreorderCode.template R
  | .member => ForcingPreorderCode.atoms R 1
  | .order => ForcingPreorderCode.atoms R 4
  | .older | .newer => ForcingAtomicCode.template equality R

private def atomIndex (k : Nat) (part : Part) : Fin (k+4) → Fin (k+7) :=
  Fin.lastCases 0 (Fin.lastCases 1 (freeIndex k part))

def sourceLeaf {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) : Part → Source.Formula (k+7)
  | .preorder => (ForcingPreorderCode.source R).rename base
  | .member => .mem 2 (carrier k)
  | .order => ReplacementPredicates.rel R params 2 4
  | .older => (ForcingAtomicCode.sourceTemplate equality R).rename (atomIndex k .older)
  | .newer => (ForcingAtomicCode.sourceTemplate equality R).rename (atomIndex k .newer)

def nativeLeaf {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) (part : Part) :
    PureSyntaxQuotation.Fm [] (fo_bound_context (k+7)) :=
  Syntax.formula (fun i => .fvar (fo_bound_variable i)) (sourceLeaf equality R part)

private theorem atom_transport {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) (part : Part) :
    (ForcingAtomicCode.template equality R).substituteMapped (atomBoundMap k) (freeMap k part) =
      Syntax.formula (fun i => .fvar (fo_bound_variable i))
        ((ForcingAtomicCode.sourceTemplate equality R).rename (atomIndex k part)) := by
  rw [ForcingAtomicCode.template_as_source, Syntax.substitute, Syntax.rename]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [ForcingAtomicCode.sourceRoles, atomIndex, Fin.lastCases_last, Term.substituteMapped] <;> rfl
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · simp only [ForcingAtomicCode.sourceRoles, atomIndex, Fin.lastCases_castSucc, Fin.lastCases_last,
        Term.substituteMapped] <;> rfl
    · simp only [ForcingAtomicCode.sourceRoles, atomIndex, Fin.lastCases_castSucc, Term.substituteMapped,
        freeMap, ForcingRelationSource.mapping_at]

theorem leaf_transport {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) (part : Part) :
    (leaf equality R part).substituteMapped (boundMap k part) (freeMap k part) = nativeLeaf equality R part := by
  cases part with
  | preorder =>
    change (ForcingPreorderCode.template R).substituteMapped ForcingRelationSource.emptyMap (freeMap k .preorder) =
      Syntax.formula (fun i => .fvar (fo_bound_variable i)) ((ForcingPreorderCode.source R).rename base)
    rw [ForcingPreorderCode.template_as_source, Syntax.rename]
    exact ForcingRelationSource.source_substitute (ForcingPreorderCode.source R) _
  | member =>
    change (ForcingPreorderCode.atoms R 1).substituteMapped _ _ =
      Syntax.formula (fun i => .fvar (fo_bound_variable i)) (.mem 2 (carrier k))
    rw [ForcingPreorderCode.atom_member_q]
    simp only [FirstOrder.Formula.substituteMapped, Arguments.substituteMapped, Term.substituteMapped, freeMap,
      ForcingRelationSource.mapping_at, freeIndex, Syntax.formula] <;> rfl
  | order =>
    change (ForcingPreorderCode.atoms R 4).substituteMapped _ _ =
      Syntax.formula (fun i => .fvar (fo_bound_variable i)) (ReplacementPredicates.rel R params 2 4)
    rw [ForcingPreorderCode.atom_qp, Syntax.substitute _ (boundMap k .order) (freeMap k .order)]
    simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, Syntax.rename]
    congr 1
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last, Term.substituteMapped] <;> rfl
    · refine Fin.lastCases ?_ (fun l => ?_) j
      · simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Term.substituteMapped] <;> rfl
      · simp only [Fin.lastCases_castSucc, Term.substituteMapped, freeMap, ForcingRelationSource.mapping_at, freeIndex, params]
  | older => exact atom_transport equality R .older
  | newer => exact atom_transport equality R .newer

def sourceBody {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) : Source.Formula (k+7) :=
  (sourceLeaf equality R .preorder).imp ((sourceLeaf equality R .member).imp
    ((sourceLeaf equality R .order).imp ((sourceLeaf equality R .older).imp (sourceLeaf equality R .newer))))

def formula {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) :
    PureSyntaxQuotation.Fm [] (fo_bound_context (k+7)) :=
  Syntax.formula (fun i => .fvar (fo_bound_variable i)) (sourceBody equality R)

def partAt : Fin 5 → Part :=
  Fin.cases .preorder (Fin.cases .member (Fin.cases .order (Fin.cases .older (fun _ => .newer))))

def tail {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) :
    Fin 5 → PureSyntaxQuotation.Fm [] (fo_bound_context (k+7)) :=
  let F := nativeLeaf equality R
  let last := F .newer
  let fourth := (F .older).imp last
  let third := (F .order).imp fourth
  let second := (F .member).imp third
  Fin.cases (formula equality R) (Fin.cases second (Fin.cases third (Fin.cases fourth (fun _ => last))))

theorem tail_imp {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) (i : Fin 4) :
    tail equality R i.castSucc =
      .imp (nativeLeaf equality R (partAt i.castSucc)) (tail equality R i.succ) := by
  refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i

theorem open_proof {k : Nat} (equality : Bool) (R : Source.Formula (k+2)) :
    FirstOrder.Derives nativeZF [] (formula equality R) := by
  apply NativeProofQuotation.from_source_closure (sourceBody equality R) (carrier k)
  apply ModelTransfer.derives
  intro M hM
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  have hm := (GodelDefOutput.close_semantics _ _).mp ((Translation.realizes_sentence M _).mp
    (ForcingAtomicBasic.monotone_body_models (M := M) equality R params (carrier k) 1 0 4 2 hM))
  intro v
  have h := hm v
  change Source.Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (sourceBody equality R)
  change Source.Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v
    (ForcingAtomicBasic.monotoneBody equality R params (carrier k) 1 0 4 2) at h
  simpa only [sourceBody, sourceLeaf, ForcingAtomicBasic.monotoneBody, Source.Formula.Realize,
    DefinableMinimaChoice.realize_rename, ForcingPreorderCode.source, ForcingAtomicBasic.preorder_semantics (M := M),
    ForcingAtomicCode.sourceTemplate, ForcingAtomicRelations.forces_semantics (M := M), params, carrier, atomIndex,
    freeIndex, Fin.lastCases_castSucc, Fin.lastCases_last] using h

end PPAC.Migration.ForcingAtomicMonoTemplate
