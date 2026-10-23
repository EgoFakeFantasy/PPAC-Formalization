import PPAC.Migration.Internal.ObjectTermImageQuotation

/-! 项像表的有限位置模式由对象全称索引/候选输出量词封闭；不抽取内部列表值。 -/
namespace PPAC.Migration.Internal.TermImageReadingSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def rows {m} : (k : Nat) → (Fin k → Formula m) → Fin m → Formula m
  | 0, _, w => .equal w w
  | k+1, ps, w => (rows k (fun i => ps i.castSucc) w).conj (ps (Fin.last k))

theorem rows_rename {m n} (k : Nat) (ps : Fin k → Formula m) (w : Fin m) (ρ : Fin m → Fin n) :
    (rows k ps w).rename ρ = rows k (fun i => (ps i).rename ρ) (ρ w) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rows, Formula.rename, ih]

theorem rows_at {m} {Γ : Context m} (k : Nat) (ps : Fin k → Formula m) (w : Fin m) (j : Fin k)
    (h : Derives Γ (rows k ps w)) : Derives Γ (ps j) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact .conjR h
    · exact ih (fun i => ps i.castSucc) i (.conjL h)

theorem intro_rows {m} {Γ : Context m} (k : Nat) (ps : Fin k → Formula m) (w : Fin m)
    (h : ∀ j, Derives Γ (ps j)) : Derives Γ (rows k ps w) := by
  induction k with
  | zero => exact .eqRefl w
  | succ k ih => exact .conjI (ih (fun i => ps i.castSucc) (fun i => h i.castSucc)) (h (Fin.last k))

def atPosition {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free))
    (w L : Fin m) (j : Fin values.length) : Formula m := .all (.all
  ((SyntaxNumeralSyntax.numeral j.val (Fin.last m).castSucc).imp
    ((StructuralListFieldSyntax.field w.castSucc.castSucc L.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
      (PureQuotationSyntax.term (values.get j) w.castSucc.castSucc (Fin.last (m+1))))))

def readings {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L : Fin m) : Formula m :=
  rows values.length (atPosition values w L) w

theorem atPosition_rename {m n} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free))
    (w L : Fin m) (j : Fin values.length) (ρ : Fin m → Fin n) :
    (atPosition values w L j).rename ρ = atPosition values (ρ w) (ρ L) j := by
  simp only [atPosition, Formula.rename, Formula.iff, SyntaxNumeralSyntax.numeral_rename,
    StructuralListFieldSyntax.field_rename, PureQuotationSyntax.term_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem readings_rename {m n} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free))
    (w L : Fin m) (ρ : Fin m → Fin n) : (readings values w L).rename ρ = readings values (ρ w) (ρ L) := by
  simp only [readings, rows_rename, atPosition_rename]

theorem at_index {m} {Γ : Context m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free))
    (w L : Fin m) (j : Fin values.length) (i q : Fin m) (hr : Derives Γ (readings values w L))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral j.val i)) :
    Derives Γ ((StructuralListFieldSyntax.field w L i q).iff (PureQuotationSyntax.term (values.get j) w q)) := by
  have hp := rows_at values.length (atPosition values w L) w j hr
  have ho := Derives.allE q (Derives.allE i hp)
  have hh : Derives Γ ((SyntaxNumeralSyntax.numeral j.val i).imp
      ((StructuralListFieldSyntax.field w L i q).iff (PureQuotationSyntax.term (values.get j) w q))) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, Formula.iff, SyntaxNumeralSyntax.numeral_rename,
      StructuralListFieldSyntax.field_rename, PureQuotationSyntax.term_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ho
  exact .impE hh hi

end PPAC.Migration.Internal.TermImageReadingSyntax
