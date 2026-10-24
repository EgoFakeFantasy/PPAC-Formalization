import PPAC.Migration.Internal.AbstractTopArgumentOperation
import PPAC.Migration.Internal.InstantiateVariableValueSyntax
import PPAC.Migration.Internal.EmptyBoundFreeInputs

/-! 待编译：mode2实际入口frame保留空绑定参数、深度对应的上下文长度、真实码表及独立数值规格。 -/
namespace PPAC.Migration.Internal.InstantiateOperationFrameSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def point {m} (bound : Bool) (w depth P a b R S i n q : Fin m) : Formula m :=
  ((Formula.mem i (SyntaxTermSyntax.limit bound a b)).conj (SyntaxVariableSyntax.code bound w i n)).imp
    ((InstantiateVariableValueSyntax.valueSpec bound w depth P i n q).iff
      (StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap bound R S) i q))

def compatible {m} (bound : Bool) (w depth P a b R S : Fin m) : Formula m := .all (.all (.all
  (point bound w.castSucc.castSucc.castSucc depth.castSucc.castSucc.castSucc P.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc
    R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))))

def closedParameter {m} (w e P : Fin m) : Formula m := .ex
  ((OmegaSyntax.empty (Fin.last m)).conj (SyntaxTermSyntax.term w.castSucc (Fin.last m) e.castSucc P.castSucc))

theorem closedParameter_rename {m l} (w e P : Fin m) (ρ : Fin m → Fin l) :
    (closedParameter w e P).rename ρ = closedParameter (ρ w) (ρ e) (ρ P) := by
  simp only [closedParameter, Formula.rename, OmegaSyntax.empty_rename, SyntaxTermSyntax.term_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_closedParameter {m} {Γ : Context m} (w e P z : Fin m)
    (hz : Derives Γ (OmegaSyntax.empty z)) (ht : Derives Γ (SyntaxTermSyntax.term w z e P)) :
    Derives Γ (closedParameter w e P) := by
  apply Derives.exI z
  simpa only [closedParameter, Formula.instantiate, Formula.rename, OmegaSyntax.empty_rename, SyntaxTermSyntax.term_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hz ht

theorem closedParameter_free {m} {Γ : Context m} (w e P : Fin m)
    (hp : Derives Γ (closedParameter w e P)) : Derives Γ (SyntaxTermSyntax.branch false w e P) := by
  let B := (OmegaSyntax.empty (Fin.last m)).conj (SyntaxTermSyntax.term w.castSucc (Fin.last m) e.castSucc P.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hp
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hf := EmptyBoundFreeInputs.term_free w.castSucc (Fin.last m) e.castSucc P.castSucc (.conjL hB) (.conjR hB)
  exact of_eq (SyntaxTermSyntax.branch_rename false w e P Fin.castSucc).symm hf

def contextsAtDepth {m} (depth a b c e : Fin m) : Formula m :=
  (OmegaSyntax.successor a depth).conj ((Formula.equal c depth).conj (.equal e b))

theorem contextsAtDepth_rename {m l} (depth a b c e : Fin m) (ρ : Fin m → Fin l) :
    (contextsAtDepth depth a b c e).rename ρ = contextsAtDepth (ρ depth) (ρ a) (ρ b) (ρ c) (ρ e) := by
  simp only [contextsAtDepth, Formula.rename, OmegaSyntax.successor_rename]

def frame {m} (w mode depth P a b c e R S : Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 2 mode).conj ((OriginalTermTraceSyntax.metadata w depth P).conj
    ((closedParameter w e P).conj ((SyntaxMixedImageCodeSyntax.termLists w a b c e R S).conj
      ((compatible true w depth P a b R S).conj
        ((compatible false w depth P a b R S).conj (contextsAtDepth depth a b c e))))))

theorem point_rename {m l} (bound : Bool) (w depth P a b R S i n q : Fin m) (ρ : Fin m → Fin l) :
    (point bound w depth P a b R S i n q).rename ρ = point bound (ρ w) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ R) (ρ S) (ρ i) (ρ n) (ρ q) := by
  simp only [point, Formula.rename, SyntaxVariableSyntax.code_rename, InstantiateVariableValueSyntax.valueSpec_rename, StructuralListFieldSyntax.field_rename]
  cases bound <;> rfl

theorem compatible_rename {m l} (bound : Bool) (w depth P a b R S : Fin m) (ρ : Fin m → Fin l) :
    (compatible bound w depth P a b R S).rename ρ = compatible bound (ρ w) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ R) (ρ S) := by
  simp only [compatible, Formula.rename, point_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem frame_rename {m l} (w mode depth P a b c e R S : Fin m) (ρ : Fin m → Fin l) :
    (frame w mode depth P a b c e R S).rename ρ = frame (ρ w) (ρ mode) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ c) (ρ e) (ρ R) (ρ S) := by
  simp only [frame, Formula.rename, SyntaxNumeralSyntax.numeral_rename, OriginalTermTraceSyntax.metadata_rename, closedParameter_rename, SyntaxMixedImageCodeSyntax.termLists_rename, compatible_rename, contextsAtDepth_rename]

theorem compatible_at {m} {Γ : Context m} (bound : Bool) (w depth P a b R S i n q : Fin m)
    (hf : Derives Γ (compatible bound w depth P a b R S))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a b))) (hn : Derives Γ (SyntaxVariableSyntax.code bound w i n)) :
    Derives Γ ((InstantiateVariableValueSyntax.valueSpec bound w depth P i n q).iff (StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap bound R S) i q)) := by
  have hh : Derives Γ (point bound w depth P a b R S i n q) := of_eq
    (by cases bound <;> simp only [point, Formula.iff, Formula.instantiate, Formula.rename, SyntaxVariableSyntax.code_rename, InstantiateVariableValueSyntax.valueSpec_rename, StructuralListFieldSyntax.field_rename, SyntaxTermSyntax.limit, SyntaxIndexMapSyntax.selectMap, Bool.false_eq_true, ite_true, ite_false, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE q (Derives.allE n (Derives.allE i hf)))
  exact .impE hh (.conjI hi hn)

theorem mode_number {m} {Γ : Context m} (w mode depth P a b c e R S : Fin m) (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (SyntaxNumeralSyntax.numeral 2 mode) := .conjL hf

theorem metadata {m} {Γ : Context m} (w mode depth P a b c e R S : Fin m) (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (OriginalTermTraceSyntax.metadata w depth P) := .conjL (.conjR hf)

theorem parameter_closed {m} {Γ : Context m} (w mode depth P a b c e R S : Fin m) (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (closedParameter w e P) := .conjL (.conjR (.conjR hf))

theorem term_lists {m} {Γ : Context m} (w mode depth P a b c e R S : Fin m) (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b c e R S) := .conjL (.conjR (.conjR (.conjR hf)))

theorem variables {m} {Γ : Context m} (bound : Bool) (w mode depth P a b c e R S : Fin m) (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (compatible bound w depth P a b R S) := by
  cases bound
  · exact .conjL (.conjR (.conjR (.conjR (.conjR (.conjR hf)))))
  · exact .conjL (.conjR (.conjR (.conjR (.conjR hf))))

theorem contexts {m} {Γ : Context m} (w mode depth P a b c e R S : Fin m) (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (contextsAtDepth depth a b c e) := .conjR (.conjR (.conjR (.conjR (.conjR (.conjR hf)))))

theorem source_successor {m} {Γ : Context m} (w mode depth P a b c e R S : Fin m) (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (OmegaSyntax.successor a depth) := .conjL (contexts w mode depth P a b c e R S hf)

theorem target_depth {m} {Γ : Context m} (w mode depth P a b c e R S : Fin m) (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (.equal c depth) := .conjL (.conjR (contexts w mode depth P a b c e R S hf))

theorem free_contexts_equal {m} {Γ : Context m} (w mode depth P a b c e R S : Fin m) (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (.equal e b) := .conjR (.conjR (contexts w mode depth P a b c e R S hf))

end PPAC.Migration.Internal.InstantiateOperationFrameSyntax
