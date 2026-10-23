import PPAC.Migration.Internal.SyntaxTopEnvironmentUnique

/-! 两类实际首槽环境的准确字段：给定项头、bound前驱/后移、free前驱及新bound0。 -/
namespace PPAC.Migration.Internal.SyntaxTopEnvironmentFields
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxTopEnvironmentSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem code_subst_output {m} {Γ : Context m} (bound : Bool) (w i n q : Fin m)
    (he : Derives Γ (.equal n q)) (hc : Derives Γ (SyntaxVariableSyntax.code bound w i n)) :
    Derives Γ (SyntaxVariableSyntax.code bound w i q) := by
  let P := SyntaxVariableSyntax.code bound w.castSucc i.castSucc (Fin.last m)
  have e0 : P.instantiate n = SyntaxVariableSyntax.code bound w i n := by
    simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate q = SyntaxVariableSyntax.code bound w i q := by
    simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

theorem code_iff_equal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w i n q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxVariableSyntax.code bound w i n)) :
    Derives Γ ((SyntaxVariableSyntax.code bound w i q).iff (.equal q n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact SyntaxVariables.unique (ZFContext.add hZ _) bound w i q n (add hw _) (.hyp (Or.inl rfl)) (add hn _)
  · apply Derives.impI
    exact code_subst_output bound w i n q (eq_symm (.hyp (Or.inl rfl))) (add hn _)

theorem instantiate_data_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t f g u i q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (instantiateData w a b A t f g u)) (hi : Derives Γ (empty i)) :
    Derives Γ ((edge f i q).iff (.equal q t)) :=
  SyntaxTermImagePrefixGraph.zero_iff hZ w u a a b t A f i q hw (.conjL (.conjR he)) hi

theorem instantiate_data_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t f g u i j q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (instantiateData w a b A t f g u))
    (hj : Derives Γ (.mem j a)) (hi : Derives Γ (successor i j)) :
    Derives Γ ((edge f i q).iff (SyntaxVariableSyntax.code true w j q)) :=
  SyntaxTypeLocalTransfer.iff_trans (SyntaxTermImagePrefixGraph.successor_iff hZ w u a a b t A f i q j hw (.conjL (.conjR he)) hj hi)
    (SyntaxVariableTableFields.identity_at hZ true w a b u j q (.conjL he) hj)

theorem instantiate_data_free {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t f g u i q : Fin m)
    (he : Derives Γ (instantiateData w a b A t f g u)) (hi : Derives Γ (.mem i b)) :
    Derives Γ ((edge g i q).iff (SyntaxVariableSyntax.code false w i q)) :=
  SyntaxVariableTableFields.identity_at hZ false w a b g i q (.conjR (.conjR he)) hi

theorem abstract_data_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B f g u z n i j q : Fin m)
    (he : Derives Γ (abstractData w a b A B f g u z n)) (hi : Derives Γ (.mem i a)) (hj : Derives Γ (successor j i)) :
    Derives Γ ((edge f i q).iff (SyntaxVariableSyntax.code true w j q)) :=
  SyntaxVariableTableFields.shifted_at hZ true w a A b f i j q (.conjL he) hi hj

theorem abstract_data_free {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B f g u z n i j q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (abstractData w a b A B f g u z n))
    (hj : Derives Γ (.mem j b)) (hi : Derives Γ (successor i j)) :
    Derives Γ ((edge g i q).iff (SyntaxVariableSyntax.code false w j q)) :=
  SyntaxTypeLocalTransfer.iff_trans (SyntaxTermImagePrefixGraph.successor_iff hZ w u b A b n B g i q j hw (.conjR (.conjR (.conjR he))) hj hi)
    (SyntaxVariableTableFields.identity_at hZ false w A b u j q (.conjL (.conjR he)) hj)

theorem abstract_data_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B f g u z n i q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (abstractData w a b A B f g u z n)) (hi : Derives Γ (empty i)) :
    Derives Γ ((edge g i q).iff (SyntaxVariableSyntax.code true w i q)) := by
  have hh := Derives.conjL (.conjR (.conjR he))
  have ez := OmegaUniversal.empty_unique z i (ZFContext.arithmetic hZ).base.extensionality (.conjL hh) hi
  have hc := SyntaxVariableImagePoint.code_subst_index true w z n i ez (.conjL (.conjR hh))
  have hq := code_iff_equal hZ true w i n q hw hc
  exact SyntaxTypeLocalTransfer.iff_trans (SyntaxTermImagePrefixGraph.zero_iff hZ w u b A b n B g i q hw (.conjR (.conjR (.conjR he))) hi)
    (.conjI (.conjR hq) (.conjL hq))

theorem instantiate_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t f g i q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (instantiateEnv w a b A t f g))
    (hi : Derives Γ (empty i)) :
    Derives Γ ((edge f i q).iff (.equal q t)) := by
  let D := instantiateBody w a b A t f g
  let Δ := Context.add D (Context.image Formula.raise (Γ))
  apply Derives.exE (p := D) he
  have hZk := ZFContext.under hZ D
  have hwk : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw D)
  have hik : Derives Δ (empty i.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (under hi D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := instantiate_data_zero hZk w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc f.castSucc g.castSucc (Fin.last m) i.castSucc q.castSucc hwk hD hik
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, edge_rename]) ho

theorem instantiate_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t f g i j q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (instantiateEnv w a b A t f g))
    (hj : Derives Γ (Formula.mem j a)) (hi : Derives Γ (successor i j)) :
    Derives Γ ((edge f i q).iff (SyntaxVariableSyntax.code true w j q)) := by
  let D := instantiateBody w a b A t f g
  let Δ := Context.add D (Context.image Formula.raise (Γ))
  apply Derives.exE (p := D) he
  have hZk := ZFContext.under hZ D
  have hwk : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw D)
  have hjk : Derives Δ (Formula.mem j.castSucc a.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under hj D)
  have hik : Derives Δ (successor i.castSucc j.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (under hi D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := instantiate_data_bound hZk w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc f.castSucc g.castSucc (Fin.last m) i.castSucc j.castSucc q.castSucc hwk hD hjk hik
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, edge_rename, SyntaxVariableSyntax.code_rename]) ho

theorem instantiate_free {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t f g i q : Fin m)
    (he : Derives Γ (instantiateEnv w a b A t f g))
    (hi : Derives Γ (Formula.mem i b)) :
    Derives Γ ((edge g i q).iff (SyntaxVariableSyntax.code false w i q)) := by
  let D := instantiateBody w a b A t f g
  let Δ := Context.add D (Context.image Formula.raise (Γ))
  apply Derives.exE (p := D) he
  have hZk := ZFContext.under hZ D
  have hik : Derives Δ (Formula.mem i.castSucc b.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under hi D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := instantiate_data_free hZk w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc f.castSucc g.castSucc (Fin.last m) i.castSucc q.castSucc hD hik
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, edge_rename, SyntaxVariableSyntax.code_rename]) ho

theorem abstract_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B f g i q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (abstractEnv w a b A B f g))
    (hi : Derives Γ (empty i)) :
    Derives Γ ((edge g i q).iff (SyntaxVariableSyntax.code true w i q)) := by
  let D := abstractBody w a b A B f g
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))
  apply eliminate_abstract w a b A B f g _ he
  have hZk := SyntaxAtomLogic.zf_under_three hZ D
  have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxAtomLogic.under_three hw D)
  have hik : Derives Δ (empty i.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (SyntaxAtomLogic.under_three hi D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := abstract_data_zero hZk w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) i.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc hwk hD hik
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, edge_rename, SyntaxVariableSyntax.code_rename]) ho

theorem abstract_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B f g i j q : Fin m)
    (he : Derives Γ (abstractEnv w a b A B f g))
    (hi : Derives Γ (Formula.mem i a)) (hj : Derives Γ (successor j i)) :
    Derives Γ ((edge f i q).iff (SyntaxVariableSyntax.code true w j q)) := by
  let D := abstractBody w a b A B f g
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))
  apply eliminate_abstract w a b A B f g _ he
  have hZk := SyntaxAtomLogic.zf_under_three hZ D
  have hik : Derives Δ (Formula.mem i.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (SyntaxAtomLogic.under_three hi D)
  have hjk : Derives Δ (successor j.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (SyntaxAtomLogic.under_three hj D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := abstract_data_bound hZk w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) i.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc hD hik hjk
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, edge_rename, SyntaxVariableSyntax.code_rename]) ho

theorem abstract_free {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B f g i j q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (abstractEnv w a b A B f g))
    (hj : Derives Γ (Formula.mem j b)) (hi : Derives Γ (successor i j)) :
    Derives Γ ((edge g i q).iff (SyntaxVariableSyntax.code false w j q)) := by
  let D := abstractBody w a b A B f g
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))
  apply eliminate_abstract w a b A B f g _ he
  have hZk := SyntaxAtomLogic.zf_under_three hZ D
  have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxAtomLogic.under_three hw D)
  have hjk : Derives Δ (Formula.mem j.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (SyntaxAtomLogic.under_three hj D)
  have hik : Derives Δ (successor i.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (SyntaxAtomLogic.under_three hi D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := abstract_data_free hZk w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) i.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc hwk hD hjk hik
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, edge_rename, SyntaxVariableSyntax.code_rename]) ho

end PPAC.Migration.Internal.SyntaxTopEnvironmentFields
