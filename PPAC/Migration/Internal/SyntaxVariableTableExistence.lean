import PPAC.Migration.Internal.SyntaxVariableTableSyntax

/-! 恒等和后移项码表实际存在；完整索引图与完整项码图均在对象层取得。 -/
namespace PPAC.Migration.Internal.SyntaxVariableTableExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxVariableTableSyntax
open SyntaxTermSyntax (contexts contexts_rename limit limit_map)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem selected_natural {m} {Γ : Context m} (bound : Bool) (w c d : Fin m) (hc : Derives Γ (contexts w c d)) :
    Derives Γ (.mem (limit bound c d) w) := by
  cases bound
  · exact .conjR hc
  · exact .conjL hc

theorem identity_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w c d : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (contexts w c d)) : Derives Γ (existsIdentity bound w c d) := by
  let R := SyntaxIdentityMapSyntax.identityMap w.castSucc (limit bound c.castSucc d.castSucc) (Fin.last m)
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (of_eq (by simp only [R, SyntaxIdentityMapSyntax.existsMap, limit_map]) (SyntaxIdentityGraph.exists_map hZ w (limit bound c d) (selected_natural bound w c d hc)))
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hc1 : Derives Ξ (contexts w.castSucc c.castSucc d.castSucc) := of_eq (contexts_rename w c d Fin.castSucc) (under hc R)
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  let F := SyntaxVariableImageSyntax.mapped bound w.castSucc.castSucc (Fin.last m).castSucc (limit bound c.castSucc.castSucc d.castSucc.castSucc) c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add F (Context.image Formula.raise Ξ)
  apply Derives.exE (p := F) (of_eq (by simp only [F, SyntaxVariableImageSyntax.existsMap, limit_map]) (SyntaxVariableImageGraph.exists_map (ZFContext.under hZ R) bound w.castSucc (Fin.last m) (limit bound c.castSucc d.castSucc) c.castSucc d.castSucc hw1 (.conjI hc1 (.conjL hR))))
  have hr2 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc (limit bound c.castSucc.castSucc d.castSucc.castSucc) (Fin.last m).castSucc) :=
    of_eq (by simp only [R, Formula.raise, SyntaxIdentityMapSyntax.identityMap_rename, limit_map]) (under hR F)
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hh := intro_identity bound w.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hr2 hF
  have ho : Derives Δ (existsIdentity bound w.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, identity_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh
  exact of_eq (by simp only [Formula.raise, existsIdentity_rename]) ho

theorem shifted_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w a c d : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (contexts w c d)) (ha : Derives Γ (.mem a w))
    (hA : Derives Γ (successor (limit bound c d) a)) : Derives Γ (existsShifted bound w a c d) := by
  let R := SyntaxFreeShiftSyntax.shiftMap w.castSucc a.castSucc (limit bound c.castSucc d.castSucc) (Fin.last m)
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (of_eq (by simp only [R, SyntaxFreeShiftSyntax.existsMap, limit_map]) (SyntaxFreeShiftGraph.exists_map hZ w a (limit bound c d) hw ha hA))
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hc1 : Derives Ξ (contexts w.castSucc c.castSucc d.castSucc) := of_eq (contexts_rename w c d Fin.castSucc) (under hc R)
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  let F := SyntaxVariableImageSyntax.mapped bound w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add F (Context.image Formula.raise Ξ)
  apply Derives.exE (p := F) (of_eq (by simp only [F, SyntaxVariableImageSyntax.existsMap]) (SyntaxVariableImageGraph.exists_map (ZFContext.under hZ R) bound w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc hw1 (.conjI hc1 (.conjL (.conjR hR)))))
  have hr2 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc a.castSucc.castSucc (limit bound c.castSucc.castSucc d.castSucc.castSucc) (Fin.last m).castSucc) :=
    of_eq (by simp only [R, Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename, limit_map]) (under hR F)
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hh := intro_shifted bound w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hr2 hF
  have ho : Derives Δ (existsShifted bound w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, shifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh
  exact of_eq (by simp only [Formula.raise, existsShifted_rename]) ho
end PPAC.Migration.Internal.SyntaxVariableTableExistence
