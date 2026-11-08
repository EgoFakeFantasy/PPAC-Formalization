import PPAC.Migration.Internal.NativeIndexFormulaQuotation

/-! Exact metadata commutation for the ORIGINAL Project.fo_formula and bound
renaming. This is consumed by the actual schema matrix quotation proof; it is
not a replacement object proof or a uniform truth predicate. -/
namespace PPAC.Migration.ProjectNativeRenaming
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project (fo_bound_context fo_bound_variable fo_term fo_formula fo_mem)
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature

private theorem map₂ {α β γ : Type} (f : α → β → γ) {a a' : α} {b b' : β}
    (ha : a = a') (hb : b = b') : f a b = f a' b' := by
  cases ha
  cases hb
  rfl

private theorem bound_index {n} (j : Fin n) : (fo_bound_variable j).index = j.val := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases rfl (fun k => ?_) j
    exact congrArg Nat.succ (ih k)

/-- The original Fin map acts on original native variables at their positions. -/
def nativeVariable {n k} (f : Fin n → Fin k) : VariableRenaming (fo_bound_context n) (fo_bound_context k) :=
  fun {sort} entry => match sort with
    | .set => fo_bound_variable (f ⟨entry.index,by simpa only [fo_bound_context,List.length_replicate] using entry.index_lt_length⟩)

theorem variable_index {n k} (f : Fin n → Fin k) (entry : FirstOrder.Variable (fo_bound_context n) SetSort.set) :
    (nativeVariable f entry).index = (f ⟨entry.index,by simpa only [fo_bound_context,List.length_replicate] using entry.index_lt_length⟩).val :=
  bound_index _

theorem variable_at {n k} (f : Fin n → Fin k) (j : Fin n) :
    nativeVariable f (fo_bound_variable j) = fo_bound_variable (f j) := by
  simp only [nativeVariable,bound_index]

private theorem variable_lift {n k} (f : Fin n → Fin k) :
    @nativeVariable (n+1) (k+1) (BoundEmbedding.lift f) = @VariableRenaming.lift SetSort (fo_bound_context n) (fo_bound_context k) SetSort.set (@nativeVariable n k f) := by
  funext sort entry
  cases sort
  cases entry with
  | here => rfl
  | there entry => rfl

private theorem lift_substitution {n k} (f : Fin n → Fin k) :
    Definitional.Term.liftSubstitution (Definitional.Term.bound ∘ f) =
      Definitional.Term.bound ∘ BoundEmbedding.lift f := by
  funext j
  refine Fin.cases rfl (fun i => ?_) j
  rfl

private theorem term_rename {n k} (f : Fin n → Fin k) (input : Definitional.Project.Term n)
    (hc : input.freeSupport = []) :
    fo_term (input.rename f) (by simpa only [Definitional.Term.freeSupport_rename] using hc) =
      (fo_term input hc).renameMapped (nativeVariable f) VariableRenaming.id := by
  cases input with
  | bound j => simp only [Definitional.Project.Term.rename,Definitional.Term.rename,Definitional.Term.bind,Function.comp_apply,fo_term,FirstOrder.Term.renameMapped,variable_at]
  | free name => change name :: [] = [] at hc; cases hc

private theorem term_weaken_rename {n k} (f : Fin n → Fin k) (input : Definitional.Project.Term n)
    (hc : input.freeSupport = []) :
    (fo_term (input.rename f) (by simpa only [Definitional.Term.freeSupport_rename] using hc)).weakenBound SetSort.set =
      ((fo_term input hc).weakenBound SetSort.set).renameMapped (VariableRenaming.lift (nativeVariable f)) VariableRenaming.id := by
  cases input with
  | bound j =>
    simp only [Definitional.Project.Term.rename,Definitional.Term.rename,Definitional.Term.bind,
      Function.comp_apply,fo_term,FirstOrder.Term.weakenBound,FirstOrder.Term.rename,Renaming.weakenBound,Renaming.bound,
      FirstOrder.Term.renameMapped,VariableRenaming.weaken,VariableRenaming.lift,variable_at]
  | free name => change name :: [] = [] at hc; cases hc

private theorem forall_rename {stage n k} (f : Fin n → Fin k) (body : Definitional.Project.Formula stage (n+1)) :
    (Definitional.Formula.forallE body).rename f = .forallE (body.rename (BoundEmbedding.lift f)) := by
  simp only [Definitional.Formula.rename,Definitional.Formula.bind,lift_substitution]

private theorem exists_rename {stage n k} (f : Fin n → Fin k) (body : Definitional.Project.Formula stage (n+1)) :
    (Definitional.Formula.existsE body).rename f = .existsE (body.rename (BoundEmbedding.lift f)) := by
  simp only [Definitional.Formula.rename,Definitional.Formula.bind,lift_substitution]

/-- ALL original Project constructors commute with original native renaming,
including the extra genuine forall introduced by the subset atom. -/
theorem formula_rename {stage n} (input : Definitional.Project.Formula stage n) :
    ∀ (hc : input.FreeClosed) {k} (f : Fin n → Fin k),
      fo_formula (input.rename f) ((Definitional.Formula.freeClosed_rename f input).mpr hc) =
        (fo_formula input hc).renameMapped (nativeVariable f) VariableRenaming.id := by
  induction input with
  | falsum =>
    intro hc k f
    simp -implicitDefEqProofs only [Definitional.Formula.rename,Definitional.Formula.bind,fo_formula,FirstOrder.Formula.renameMapped]
  | truth =>
    intro hc k f
    simp -implicitDefEqProofs only [Definitional.Formula.rename,Definitional.Formula.bind,fo_formula,FirstOrder.Formula.renameMapped]
  | mem left right =>
    intro hc k f
    simp only [Definitional.Formula.FreeClosed] at hc
    simpa -implicitDefEqProofs only [Definitional.Formula.rename,Definitional.Formula.bind,fo_formula,
      Definitional.Project.Term.rename,Definitional.Term.rename,fo_mem,FirstOrder.Formula.renameMapped,
      FirstOrder.Arguments.renameMapped] using map₂ fo_mem (term_rename f left hc.1) (term_rename f right hc.2)
  | atom symbol hs args =>
    intro hc k f
    simp only [Definitional.Formula.FreeClosed] at hc
    cases symbol with
    | extensionalEq =>
      simpa -implicitDefEqProofs only [Definitional.Formula.rename,Definitional.Formula.bind,
        fo_formula,Definitional.TermVector.get_bind,Definitional.Project.Term.rename,Definitional.Term.rename,
        FirstOrder.Formula.renameMapped] using map₂ FirstOrder.Formula.equal
          (term_rename f (args 0) (hc 0)) (term_rename f (args 1) (hc 1))
    | subset =>
      have h0 := term_weaken_rename f (args 0) (hc 0)
      have h1 := term_weaken_rename f (args 1) (hc 1)
      have hBody := map₂ FirstOrder.Formula.imp
        (congrArg (fun t => fo_mem (.bvar (.here : FirstOrder.Variable (SetSort.set :: fo_bound_context k) SetSort.set)) t) h0)
        (congrArg (fun t => fo_mem (.bvar (.here : FirstOrder.Variable (SetSort.set :: fo_bound_context k) SetSort.set)) t) h1)
      simpa -implicitDefEqProofs only [Definitional.Formula.rename,Definitional.Formula.bind,
        fo_formula,Definitional.TermVector.get_bind,Definitional.Project.Term.rename,Definitional.Term.rename,
        FirstOrder.Formula.renameMapped,fo_mem,FirstOrder.Arguments.renameMapped,FirstOrder.Term.renameMapped,
        VariableRenaming.lift] using congrArg (fun p : FirstOrder.Formula ℒ (SetSort.set :: fo_bound_context k) [] => @FirstOrder.Formula.forallE ℒ (fo_bound_context k) [] SetSort.set p) hBody
  | neg body ih =>
    intro hc k f
    simp only [Definitional.Formula.FreeClosed] at hc
    simpa -implicitDefEqProofs only [Definitional.Formula.rename,Definitional.Formula.bind,fo_formula,
      FirstOrder.Formula.renameMapped] using congrArg FirstOrder.Formula.neg (ih hc f)
  | conj left right ihL ihR =>
    intro hc k f
    simp only [Definitional.Formula.FreeClosed] at hc
    simpa -implicitDefEqProofs only [Definitional.Formula.rename,Definitional.Formula.bind,fo_formula,
      FirstOrder.Formula.renameMapped] using map₂ FirstOrder.Formula.conj (ihL hc.1 f) (ihR hc.2 f)
  | disj left right ihL ihR =>
    intro hc k f
    simp only [Definitional.Formula.FreeClosed] at hc
    simpa -implicitDefEqProofs only [Definitional.Formula.rename,Definitional.Formula.bind,fo_formula,
      FirstOrder.Formula.renameMapped] using map₂ FirstOrder.Formula.disj (ihL hc.1 f) (ihR hc.2 f)
  | imp left right ihL ihR =>
    intro hc k f
    simp only [Definitional.Formula.FreeClosed] at hc
    simpa -implicitDefEqProofs only [Definitional.Formula.rename,Definitional.Formula.bind,fo_formula,
      FirstOrder.Formula.renameMapped] using map₂ FirstOrder.Formula.imp (ihL hc.1 f) (ihR hc.2 f)
  | iff left right ihL ihR =>
    intro hc k f
    simp only [Definitional.Formula.FreeClosed] at hc
    simpa -implicitDefEqProofs only [Definitional.Formula.rename,Definitional.Formula.bind,fo_formula,
      FirstOrder.Formula.renameMapped] using map₂ FirstOrder.Formula.iff (ihL hc.1 f) (ihR hc.2 f)
  | forallE body ih =>
    intro hc k f
    simp only [Definitional.Formula.FreeClosed] at hc
    simpa -implicitDefEqProofs only [forall_rename,fo_formula,FirstOrder.Formula.renameMapped,variable_lift] using
      congrArg (fun p : FirstOrder.Formula ℒ (SetSort.set :: fo_bound_context k) [] => @FirstOrder.Formula.forallE ℒ (fo_bound_context k) [] SetSort.set p) (ih hc (BoundEmbedding.lift f))
  | existsE body ih =>
    intro hc k f
    simp only [Definitional.Formula.FreeClosed] at hc
    simpa -implicitDefEqProofs only [exists_rename,fo_formula,FirstOrder.Formula.renameMapped,variable_lift] using
      congrArg (fun p : FirstOrder.Formula ℒ (SetSort.set :: fo_bound_context k) [] => @FirstOrder.Formula.existsE ℒ (fo_bound_context k) [] SetSort.set p) (ih hc (BoundEmbedding.lift f))

/-- Reuse the original native rename/substitution equivalence, rather than
reproving native formula recursion. -/
theorem formula_substitute {stage n k} (input : Definitional.Project.Formula stage n)
    (hc : input.FreeClosed) (f : Fin n → Fin k) :
    (fo_formula input hc).substituteMapped (fun entry => .bvar (nativeVariable f entry)) (fun entry => .fvar entry) =
      fo_formula (input.rename f) ((Definitional.Formula.freeClosed_rename f input).mpr hc) :=
  (FirstOrder.Formula.renameMapped_eq_substituteMapped (nativeVariable f) VariableRenaming.id (fo_formula input hc)).symm.trans
    (formula_rename input hc f).symm

end PPAC.Migration.ProjectNativeRenaming
