import PPAC.Migration.Internal.AbstractTopArgumentOperation
import PPAC.Migration.Internal.AbstractBinderVariable

/-! 任意内部深度的mode1兼容frame：真实有类型码表及全部作用域变量的独立数值对应。 -/
namespace PPAC.Migration.Internal.AbstractOperationFrameSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def point {m} (bound : Bool) (w depth a b R S i n q : Fin m) : Formula m :=
  ((Formula.mem i (SyntaxTermSyntax.limit bound a b)).conj (SyntaxVariableSyntax.code bound w i n)).imp
    ((AbstractVariableValueSyntax.valueSpec bound w depth i n q).iff
      (StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap bound R S) i q))

def compatible {m} (bound : Bool) (w depth a b R S : Fin m) : Formula m := .all (.all (.all
  (point bound w.castSucc.castSucc.castSucc depth.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc
    R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))))

def frame {m} (w mode depth P a b c e R S : Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 1 mode).conj ((OriginalTermTraceSyntax.metadata w depth P).conj
    ((SyntaxMixedImageCodeSyntax.termLists w a b c e R S).conj
      ((compatible true w depth a b R S).conj (compatible false w depth a b R S))))

theorem point_rename {m l} (bound : Bool) (w depth a b R S i n q : Fin m) (ρ : Fin m → Fin l) :
    (point bound w depth a b R S i n q).rename ρ = point bound (ρ w) (ρ depth) (ρ a) (ρ b) (ρ R) (ρ S) (ρ i) (ρ n) (ρ q) := by
  simp only [point, Formula.rename, SyntaxVariableSyntax.code_rename, AbstractVariableValueSyntax.valueSpec_rename, StructuralListFieldSyntax.field_rename]
  cases bound <;> rfl

theorem compatible_rename {m l} (bound : Bool) (w depth a b R S : Fin m) (ρ : Fin m → Fin l) :
    (compatible bound w depth a b R S).rename ρ = compatible bound (ρ w) (ρ depth) (ρ a) (ρ b) (ρ R) (ρ S) := by
  simp only [compatible, Formula.rename, point_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem frame_rename {m l} (w mode depth P a b c e R S : Fin m) (ρ : Fin m → Fin l) :
    (frame w mode depth P a b c e R S).rename ρ = frame (ρ w) (ρ mode) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ c) (ρ e) (ρ R) (ρ S) := by
  simp only [frame, Formula.rename, SyntaxNumeralSyntax.numeral_rename, OriginalTermTraceSyntax.metadata_rename, SyntaxMixedImageCodeSyntax.termLists_rename, compatible_rename]

theorem compatible_at {m} {Γ : Context m} (bound : Bool) (w depth a b R S i n q : Fin m)
    (hf : Derives Γ (compatible bound w depth a b R S))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a b))) (hn : Derives Γ (SyntaxVariableSyntax.code bound w i n)) :
    Derives Γ ((AbstractVariableValueSyntax.valueSpec bound w depth i n q).iff (StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap bound R S) i q)) := by
  have hh : Derives Γ (point bound w depth a b R S i n q) := of_eq
    (by cases bound <;> simp only [point, Formula.iff, Formula.instantiate, Formula.rename, SyntaxVariableSyntax.code_rename, AbstractVariableValueSyntax.valueSpec_rename, StructuralListFieldSyntax.field_rename, SyntaxTermSyntax.limit, SyntaxIndexMapSyntax.selectMap, Bool.false_eq_true, ite_true, ite_false, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE q (Derives.allE n (Derives.allE i hf)))
  exact .impE hh (.conjI hi hn)

theorem mode_number {m} {Γ : Context m} (w mode depth P a b c e R S : Fin m) (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (SyntaxNumeralSyntax.numeral 1 mode) := .conjL hf

theorem metadata {m} {Γ : Context m} (w mode depth P a b c e R S : Fin m) (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (OriginalTermTraceSyntax.metadata w depth P) := .conjL (.conjR hf)

theorem term_lists {m} {Γ : Context m} (w mode depth P a b c e R S : Fin m) (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b c e R S) := .conjL (.conjR (.conjR hf))

theorem variables {m} {Γ : Context m} (bound : Bool) (w mode depth P a b c e R S : Fin m) (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (compatible bound w depth a b R S) := by
  cases bound
  · exact .conjR (.conjR (.conjR (.conjR hf)))
  · exact .conjL (.conjR (.conjR (.conjR hf)))

end PPAC.Migration.Internal.AbstractOperationFrameSyntax
