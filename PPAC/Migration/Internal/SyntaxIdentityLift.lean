import PPAC.Migration.Internal.SyntaxIdentityCode

/-! 恒等实际图及自然映射码的binder提升保持恒等；所有后继和边均在对象层。 -/
namespace PPAC.Migration.Internal.SyntaxIdentityLift
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax
open SyntaxRenameTermIdentity SyntaxIndexLiftSyntax SyntaxMapCodeSyntax SyntaxIdentityMapSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem successor_subst {m} {Γ : Context m} (i k l : Fin m)
    (he : Derives Γ (.equal k l)) (hi : Derives Γ (successor i k)) : Derives Γ (successor i l) := by
  let P := successor i.castSucc (Fin.last m)
  have e0 : P.instantiate k = successor i k := by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate l = successor i l := by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hi))

theorem value_diagonal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (r a i j : Fin m)
    (hd : Derives Γ (diagonal r)) (hv : Derives Γ (value r a i j)) : Derives Γ (.equal i j) := by
  apply Derives.disjE hv
  · let E := (empty i).conj (empty j)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact OmegaUniversal.empty_unique i j (ZFContext.arithmetic (ZFContext.add hZ E)).base.extensionality (.conjL hE) (.conjR hE)
  · let X := shifted r a i j
    let B := shiftBody r a i j
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.add X Γ)))
    apply eliminate_shifted r a i j _ (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hd2 : Derives Δ (diagonal r.castSucc.castSucc) := of_eq (by simp only [Formula.raise, diagonal_rename]) (SyntaxRenameBinders.under_2 (add hd X) B)
    have he := diagonal_at _ _ _ hd2 (.conjR (.conjL hB))
    have hi := successor_subst _ _ _ he (.conjL (.conjR hB))
    exact InsertLogic.unique i.castSucc.castSucc j.castSucc.castSucc (Fin.last (m+1)) (Fin.last (m+1))
      (ZFContext.arithmetic (SyntaxRenameBinders.zf_under_2 (ZFContext.add hZ X) B)).base.extensionality hi (.conjR (.conjR hB))

theorem graph_diagonal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c u v g : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (diagonal r)) (hl : Derives Γ (lifted w r a c u v g)) : Derives Γ (diagonal g) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw E)
  have hd2 : Derives Δ (diagonal r.castSucc.castSucc) := of_eq (by simp only [Formula.raise, diagonal_rename]) (SyntaxRenameBinders.under_2 hd E)
  have hl2 : Derives Δ (lifted w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc u.castSucc.castSucc v.castSucc.castSucc g.castSucc.castSucc) := of_eq (by simp only [Formula.raise, lifted_rename]) (SyntaxRenameBinders.under_2 hl E)
  have hv := Derives.impE (.conjL (SyntaxIndexLift.edge_iff hZ2 _ _ _ _ _ _ _ _ _ hw2 hl2)) (Derives.hyp (Or.inl rfl) : Derives Δ E)
  exact value_diagonal hZ2 _ _ _ _ hd2 hv

theorem code_same_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a R u L : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (identityCode w a R))
    (hl : Derives Γ (SyntaxMapLiftSyntax.codedLift w a a R u u L)) : Derives Γ (identityCode w u L) := by
  let B := SyntaxMapLiftSyntax.body w a a R u u L
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxMapLiftSyntax.eliminate_lift w a a R u u L _ hl
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi2 : Derives Δ (identityCode w.castSucc.castSucc a.castSucc.castSucc R.castSucc.castSucc) := of_eq (by simp only [Formula.raise, identityCode_rename]) (SyntaxRenameBinders.under_2 hi B)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hd := SyntaxIdentityCode.at_graph hZ2 _ _ _ _ hi2 (.conjL hB)
  have hg := graph_diagonal hZ2 _ _ _ _ _ _ _ hw2 hd (.conjL (.conjR hB))
  have ho := SyntaxIdentityMapSyntax.intro_code w.castSucc.castSucc u.castSucc.castSucc (Fin.last (m+1)) L.castSucc.castSucc (.conjR (.conjR hB)) hg
  exact of_eq (by simp only [Formula.raise, identityCode_rename]) ho
theorem code_lift {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a R u v L : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (identityCode w a R))
    (hl : Derives Γ (SyntaxMapLiftSyntax.codedLift w a a R u v L)) : Derives Γ ((Formula.equal u v).conj (identityCode w u L)) := by
  have hp := SyntaxMapLiftParameters.successors w a a R u v L hl
  have he := InsertLogic.unique u v a a (ZFContext.arithmetic hZ).base.extensionality (.conjL hp) (.conjR hp)
  have hs := SyntaxMapLiftParameters.subst_v w a a R u v L u (eq_symm he) hl
  exact .conjI he (code_same_successor hZ w a R u L hw hi hs)
end PPAC.Migration.Internal.SyntaxIdentityLift
