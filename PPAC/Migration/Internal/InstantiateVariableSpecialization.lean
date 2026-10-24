import PPAC.Migration.Internal.InstantiateVariableValueSyntax
import PPAC.Migration.Internal.NaturalOrderBasic

/-! 原 mode2 独立数值规格在阈值点和深度以内的对象化简。 -/
namespace PPAC.Migration.Internal.InstantiateVariableSpecialization
open Source SourceAlgebra SourceLogic OmegaSyntax InstantiateVariableValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem tail_not_at_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d i y : Fin m)
    (he : Derives Γ (.equal i d)) (ht : Derives Γ (boundTail w d i y)) : Derives Γ .bot := by
  let B := (successor i.castSucc (Fin.last m)).conj ((Formula.mem d.castSucc i.castSucc).conj
    (SyntaxVariableSyntax.code true w.castSucc (Fin.last m) y.castSucc))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have he1 : Derives Δ (.equal i.castSucc d.castSucc) := under he B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hn := NaturalOrderBasic.nonself (ZFContext.under hZ B) d.castSucc
  exact .impE hn (UnorderedPairLogic.mem_container_subst i.castSucc d.castSucc d.castSucc he1 (.conjL (.conjR hB)))

theorem at_point_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d P i x y : Fin m)
    (he : Derives Γ (.equal i d)) : Derives Γ ((boundValue w d P i x y).iff (.equal y P)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := boundValue w d P i x y
    apply Derives.disjE (.hyp (Γ := Context.add E Γ) (Or.inl rfl))
    · exact .botE (.impE (add (add (NaturalOrderBasic.nonself hZ d) E) _)
        (mem_subst (add (add he E) _) (.conjL (.hyp (Or.inl rfl)))))
    · apply Derives.disjE (.hyp (Or.inl rfl))
      · exact .conjR (.hyp (Or.inl rfl))
      · exact .botE (tail_not_at_point (ZFContext.add (ZFContext.add (ZFContext.add hZ E) _) _) w d i y
          (add (add (add he E) _) _) (.hyp (Or.inl rfl)))
  · exact .impI (.disjR (.disjL (.conjI (add he _) (.hyp (Or.inl rfl)))))

theorem below_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d P i x y : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (hi : Derives Γ (.mem i d)) :
    Derives Γ ((boundValue w d P i x y).iff (.equal y x)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := boundValue w d P i x y
    apply Derives.disjE (.hyp (Γ := Context.add E Γ) (Or.inl rfl))
    · exact .conjR (.hyp (Or.inl rfl))
    · apply Derives.disjE (.hyp (Or.inl rfl))
      · exact .botE (.impE (add (add (add (NaturalOrderBasic.nonself hZ d) E) _) _)
          (mem_subst (.conjL (.hyp (Or.inl rfl))) (add (add (add hi E) _) _)))
      · let F := boundTail w d i y
        let B := (successor i.castSucc (Fin.last m)).conj ((Formula.mem d.castSucc i.castSucc).conj
          (SyntaxVariableSyntax.code true w.castSucc (Fin.last m) y.castSucc))
        let Δ := Context.add B (Context.image Formula.raise (Context.add F (Context.add (((Formula.equal i d).conj (.equal y P)).disj (boundTail w d i y)) (Context.add E Γ))))
        apply Derives.exE (p := B) (.hyp (Or.inl rfl))
        have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add (add (add hw E) _) F) B)
        have hd1 : Derives Δ (.mem d.castSucc w.castSucc) := under (add (add (add hd E) _) F) B
        have hi1 : Derives Δ (.mem i.castSucc d.castSucc) := under (add (add (add hi E) _) F) B
        have hB : Derives Δ B := .hyp (Or.inl rfl)
        exact .botE (NaturalOrderBasic.below_not_reverse (ZFContext.under (ZFContext.add (ZFContext.add (ZFContext.add hZ E) _) F) B)
          w.castSucc d.castSucc i.castSucc hw1 hd1 (.disjR (.conjL (.conjR hB))) hi1)
  · exact .impI (.disjL (.conjI (add hi _) (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.InstantiateVariableSpecialization
