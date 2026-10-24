import PPAC.Migration.Internal.ProjectAtomicSyntax

/-! Membership conversion inserts the actual relation leaf; all candidates are covered. -/
namespace PPAC.Migration.Internal.ProjectAtomicMember
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectAtomicSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem target_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y q : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (SyntaxTermSyntax.term w b f x))
    (hy : Derives Γ (SyntaxTermSyntax.term w b f y)) (hr : Derives Γ (memberResult w x y q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w q b f) := by
  let S := (SyntaxAtomSyntax.zeroScalar w.castSucc (Fin.last m)).conj
    (SyntaxAtomSyntax.memberCode w.castSucc (Fin.last m) x.castSucc y.castSucc q.castSucc)
  let Δ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) hr
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw S)
  have hx1 := of_eq (SyntaxTermSyntax.term_rename w b f x Fin.castSucc) (under hx S)
  have hy1 := of_eq (SyntaxTermSyntax.term_rename w b f y Fin.castSucc) (under hy S)
  have hi := FormulaCodeKnownAtomic.member_iff (ZFContext.under hZ S) w.castSucc b.castSucc f.castSucc (Fin.last m) x.castSucc y.castSucc q.castSucc hw1 (.conjR hS)
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w q b f Fin.castSucc).symm (.impE (.conjR hi) (.conjI (.conjL hS) (.conjI hx1 hy1)))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y q r : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (memberResult w x y q)) (hr : Derives Γ (memberResult w x y r)) :
    Derives Γ (.equal q r) := by
  let S := (SyntaxAtomSyntax.zeroScalar w.castSucc (Fin.last m)).conj
    (SyntaxAtomSyntax.memberCode w.castSucc (Fin.last m) x.castSucc y.castSucc q.castSucc)
  let Δ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) hq
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hr1 := of_eq (memberResult_rename w x y r Fin.castSucc) (under hr S)
  let T := (SyntaxAtomSyntax.zeroScalar w.castSucc.castSucc (Fin.last (m+1))).conj
    (SyntaxAtomSyntax.memberCode w.castSucc.castSucc (Fin.last (m+1)) x.castSucc.castSucc y.castSucc.castSucc r.castSucc.castSucc)
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) hr1
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ S) T
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under (under hw S) T
  have hS2 : Derives Ξ ((SyntaxAtomSyntax.zeroScalar w.castSucc.castSucc (Fin.last m).castSucc).conj
      (SyntaxAtomSyntax.memberCode w.castSucc.castSucc (Fin.last m).castSucc x.castSucc.castSucc y.castSucc.castSucc q.castSucc.castSucc)) := by
    simpa only [S, Formula.raise, Formula.rename, SyntaxAtomSyntax.zeroScalar_rename, SyntaxAtomSyntax.memberCode_rename] using under hS T
  have hs := SyntaxConstructors.unique hZ2 0 0 w.castSucc.castSucc Fin.elim0 (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjL hS2) (.conjL hT)
  have hc := ProjectSubsetPoint.inputs3_subst 2 w.castSucc.castSucc (Fin.last m).castSucc x.castSucc.castSucc y.castSucc.castSucc
    (Fin.last (m+1)) x.castSucc.castSucc y.castSucc.castSucc q.castSucc.castSucc hs (.eqRefl _) (.eqRefl _) (.conjR hS2)
  exact SyntaxConstructors.unique hZ2 3 2 w.castSucc.castSucc (SyntaxAtomSyntax.three (Fin.last (m+1)) x.castSucc.castSucc y.castSucc.castSucc)
    q.castSucc.castSucc r.castSucc.castSucc hw2 hc (.conjR hT)

theorem exists_result {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (SyntaxTermSyntax.term w b f x))
    (hy : Derives Γ (SyntaxTermSyntax.term w b f y)) : Derives Γ (existsResult 0 w b f x y) := by
  have hxW := SyntaxTerms.range hZ w b f x hw hx
  have hyW := SyntaxTerms.range hZ w b f y hw hy
  let S := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxAtomSyntax.zeroScalar w.castSucc (Fin.last m))
  let Δ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) (SyntaxConstructors.exists_constructor hZ 0 0 w Fin.elim0 hw (.eqRefl w))
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw S)
  have hi : Derives Δ (SyntaxForestSyntax.inputs 3 w.castSucc (SyntaxAtomSyntax.three (Fin.last m) x.castSucc y.castSucc)) :=
    .conjI (.conjL hS) (.conjI (under hxW S) (.conjI (under hyW S) (.eqRefl w.castSucc)))
  let Q := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (SyntaxAtomSyntax.memberCode w.castSucc.castSucc (Fin.last m).castSucc x.castSucc.castSucc y.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add Q (Context.image Formula.raise Δ)
  apply Derives.exE (p := Q) (SyntaxConstructors.exists_constructor (ZFContext.under hZ S) 3 2 w.castSucc (SyntaxAtomSyntax.three (Fin.last m) x.castSucc y.castSucc) hw1 hi)
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hs2 : Derives Ξ (SyntaxAtomSyntax.zeroScalar w.castSucc.castSucc (Fin.last m).castSucc) :=
    of_eq (SyntaxAtomSyntax.zeroScalar_rename w.castSucc (Fin.last m) Fin.castSucc) (under (Derives.conjR hS) Q)
  have hr : Derives Ξ (memberResult w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc (Fin.last (m+1))) := by
    apply Derives.exI (Fin.last m).castSucc
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxAtomSyntax.zeroScalar_rename, SyntaxAtomSyntax.memberCode_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hs2 (.conjR hQ))
  have ho := intro_result 0 w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc (Fin.last (m+1)) (.conjL hQ) hr
  exact of_eq (by simp only [Formula.raise, existsResult_rename]) ho

end PPAC.Migration.Internal.ProjectAtomicMember
