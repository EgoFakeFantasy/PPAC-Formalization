import PPAC.Migration.Internal.FormulaTransformOperatorSyntax

/-! 原19条对象规则内的全称／蕴含双条件同余，用于实际递归图传输。 -/
namespace PPAC.Migration.Internal.FormulaTransformCongruence
open Source SourceAlgebra SourceLogic FormulaCodeCongruence SyntaxTypeLocalTransfer
open SyntaxRenameQuerySyntax (of_eq)

theorem imp_congr {m} {Γ : Context m} {p p' q q' : Formula m}
    (hp : Derives Γ (p.iff p')) (hq : Derives Γ (q.iff q')) :
    Derives Γ ((p.imp q).iff (p'.imp q')) := by
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.impI
    have hP : Derives (Context.add p' (Context.add (p.imp q) Γ)) p :=
      .impE (add (add (.conjR hp) _) _) (.hyp (Or.inl rfl))
    exact .impE (add (add (.conjL hq) _) _) (.impE (.hyp (Or.inr (Or.inl rfl))) hP)
  · apply Derives.impI
    apply Derives.impI
    have hP : Derives (Context.add p (Context.add (p'.imp q') Γ)) p' :=
      .impE (add (add (.conjL hp) _) _) (.hyp (Or.inl rfl))
    exact .impE (add (add (.conjR hq) _) _) (.impE (.hyp (Or.inr (Or.inl rfl))) hP)

theorem iff_congr {m} {Γ : Context m} {p p' q q' : Formula m}
    (hp : Derives Γ (p.iff p')) (hq : Derives Γ (q.iff q')) :
    Derives Γ ((p.iff q).iff (p'.iff q')) := conj_congr (imp_congr hp hq) (imp_congr hq hp)

theorem all_congr {m} {Γ : Context m} {p q : Formula (m+1)}
    (hh : Derives (Context.image Formula.raise Γ) (p.iff q)) :
    Derives Γ ((Formula.all p).iff (.all q)) := by
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.allI
    have hAll : Derives (Context.image Formula.raise (Context.add (.all p) Γ)) ((Formula.all p).rename Fin.castSucc) :=
      .rename Fin.castSucc (.hyp (Or.inl rfl))
    have hP := of_eq (ex_raise_instance p) (Derives.allE (Fin.last m) hAll)
    have hPQ : Derives (Context.image Formula.raise (Context.add (.all p) Γ)) (p.imp q) := by
      apply Derives.weaken _ (.conjL hh)
      rintro s ⟨t, ht, he⟩
      exact ⟨t, Or.inr ht, he⟩
    exact .impE hPQ hP
  · apply Derives.impI
    apply Derives.allI
    have hAll : Derives (Context.image Formula.raise (Context.add (.all q) Γ)) ((Formula.all q).rename Fin.castSucc) :=
      .rename Fin.castSucc (.hyp (Or.inl rfl))
    have hQ := of_eq (ex_raise_instance q) (Derives.allE (Fin.last m) hAll)
    have hQP : Derives (Context.image Formula.raise (Context.add (.all q) Γ)) (q.imp p) := by
      apply Derives.weaken _ (.conjR hh)
      rintro s ⟨t, ht, he⟩
      exact ⟨t, Or.inr ht, he⟩
    exact .impE hQP hQ

end PPAC.Migration.Internal.FormulaTransformCongruence
