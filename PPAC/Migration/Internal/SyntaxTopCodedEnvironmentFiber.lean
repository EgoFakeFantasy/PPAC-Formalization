import PPAC.Migration.Internal.SyntaxTopCodedEnvironmentFields

/-! 两类数值首槽环境的实际唯一纤维及精确输入双条件。 -/
namespace PPAC.Migration.Internal.SyntaxTopCodedEnvironmentFiber
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopCodedEnvironmentSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def instantiateUnique {m} (w a b A t R S : Fin m) : Formula m := .all (.all
  ((instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    ((Formula.equal (Fin.last m).castSucc R.castSucc.castSucc).conj (.equal (Fin.last (m+1)) S.castSucc.castSucc))))

def instantiateFiber {m} (w a b A t : Fin m) : Formula m := .ex (.ex
  ((instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (instantiateUnique w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))

theorem instantiateUnique_rename {m k} (w a b A t R S : Fin m) (ρ : Fin m → Fin k) :
    (instantiateUnique w a b A t R S).rename ρ = instantiateUnique (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ R) (ρ S) := by
  simp only [instantiateUnique, Formula.rename, instantiateCoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem instantiateFiber_rename {m k} (w a b A t : Fin m) (ρ : Fin m → Fin k) :
    (instantiateFiber w a b A t).rename ρ = instantiateFiber (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) := by
  simp only [instantiateFiber, Formula.rename, instantiateCoded_rename, instantiateUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem instantiate_unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t R S : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (instantiateCoded w a b A t R S)) : Derives Γ (instantiateUnique w a b A t R S) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let Q := instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add Q (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ Q
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw Q)
  have hc2 : Derives Δ (instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, instantiateCoded_rename]) (SyntaxRenameBinders.under_2 hc Q)
  exact SyntaxTopCodedEnvironmentUnique.instantiate_unique hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) R.castSucc.castSucc S.castSucc.castSucc hw2 (.hyp (Or.inl rfl)) hc2

theorem instantiate_actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t)) : Derives Γ (instantiateFiber w a b A t) := by
  let Q := instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add Q (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 Q _ (SyntaxTopCodedEnvironmentExistence.instantiate_exists hZ w a b A t hw hi)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ Q
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hu := instantiate_unique_output hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hQ
  have ho : Derives Δ (instantiateFiber w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc) := by
    apply Derives.exI (Fin.last m).castSucc
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Q, Formula.instantiate, Formula.rename, instantiateCoded_rename, instantiateUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hQ hu)
  exact of_eq (by simp only [Formula.raise, instantiateFiber_rename]) ho

theorem instantiate_input_of_exists {m} {Γ : Context m} (w a b A t : Fin m)
    (he : Derives Γ (existsInstantiate w a b A t)) : Derives Γ (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t) := by
  let Q := instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add Q (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 Q _ he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have ho := SyntaxTopCodedEnvironmentTyping.instantiate_input w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hQ
  exact of_eq (by simp only [Formula.raise, SyntaxTopEnvironmentSyntax.instantiateInput_rename]) ho

theorem instantiate_exists_of_fiber {m} {Γ : Context m} (w a b A t : Fin m)
    (he : Derives Γ (instantiateFiber w a b A t)) : Derives Γ (existsInstantiate w a b A t) := by
  let Q := (instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (instantiateUnique w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add Q (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 Q _ he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have ho := intro_instantiate_pair w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjL hQ)
  exact of_eq (by simp only [Formula.raise, existsInstantiate_rename]) ho

theorem instantiate_exists_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((existsInstantiate w a b A t).iff (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact instantiate_input_of_exists w a b A t (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact SyntaxTopCodedEnvironmentExistence.instantiate_exists (ZFContext.add hZ _) w a b A t (add hw _) (.hyp (Or.inl rfl))

theorem instantiate_fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((instantiateFiber w a b A t).iff (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact instantiate_input_of_exists w a b A t (instantiate_exists_of_fiber w a b A t (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact instantiate_actual_fiber (ZFContext.add hZ _) w a b A t (add hw _) (.hyp (Or.inl rfl))

def abstractUnique {m} (w a b A B R S : Fin m) : Formula m := .all (.all
  ((abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    ((Formula.equal (Fin.last m).castSucc R.castSucc.castSucc).conj (.equal (Fin.last (m+1)) S.castSucc.castSucc))))

def abstractFiber {m} (w a b A B : Fin m) : Formula m := .ex (.ex
  ((abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (abstractUnique w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))

theorem abstractUnique_rename {m k} (w a b A B R S : Fin m) (ρ : Fin m → Fin k) :
    (abstractUnique w a b A B R S).rename ρ = abstractUnique (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ R) (ρ S) := by
  simp only [abstractUnique, Formula.rename, abstractCoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem abstractFiber_rename {m k} (w a b A B : Fin m) (ρ : Fin m → Fin k) :
    (abstractFiber w a b A B).rename ρ = abstractFiber (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) := by
  simp only [abstractFiber, Formula.rename, abstractCoded_rename, abstractUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem abstract_unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B R S : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (abstractCoded w a b A B R S)) : Derives Γ (abstractUnique w a b A B R S) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let Q := abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add Q (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ Q
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw Q)
  have hc2 : Derives Δ (abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, abstractCoded_rename]) (SyntaxRenameBinders.under_2 hc Q)
  exact SyntaxTopCodedEnvironmentUnique.abstract_unique hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) R.castSucc.castSucc S.castSucc.castSucc hw2 (.hyp (Or.inl rfl)) hc2

theorem abstract_actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B)) : Derives Γ (abstractFiber w a b A B) := by
  let Q := abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add Q (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 Q _ (SyntaxTopCodedEnvironmentExistence.abstract_exists hZ w a b A B hw hi)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ Q
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hu := abstract_unique_output hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hQ
  have ho : Derives Δ (abstractFiber w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc) := by
    apply Derives.exI (Fin.last m).castSucc
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Q, Formula.instantiate, Formula.rename, abstractCoded_rename, abstractUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hQ hu)
  exact of_eq (by simp only [Formula.raise, abstractFiber_rename]) ho

theorem abstract_input_of_exists {m} {Γ : Context m} (w a b A B : Fin m)
    (he : Derives Γ (existsAbstract w a b A B)) : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) := by
  let Q := abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add Q (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 Q _ he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have ho := SyntaxTopCodedEnvironmentTyping.abstract_input w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hQ
  exact of_eq (by simp only [Formula.raise, SyntaxTopEnvironmentSyntax.abstractInput_rename]) ho

theorem abstract_exists_of_fiber {m} {Γ : Context m} (w a b A B : Fin m)
    (he : Derives Γ (abstractFiber w a b A B)) : Derives Γ (existsAbstract w a b A B) := by
  let Q := (abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (abstractUnique w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add Q (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 Q _ he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have ho := intro_abstract_pair w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjL hQ)
  exact of_eq (by simp only [Formula.raise, existsAbstract_rename]) ho

theorem abstract_exists_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((existsAbstract w a b A B).iff (SyntaxTopEnvironmentSyntax.abstractInput w a b A B)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact abstract_input_of_exists w a b A B (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact SyntaxTopCodedEnvironmentExistence.abstract_exists (ZFContext.add hZ _) w a b A B (add hw _) (.hyp (Or.inl rfl))

theorem abstract_fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((abstractFiber w a b A B).iff (SyntaxTopEnvironmentSyntax.abstractInput w a b A B)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact abstract_input_of_exists w a b A B (abstract_exists_of_fiber w a b A B (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact abstract_actual_fiber (ZFContext.add hZ _) w a b A B (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxTopCodedEnvironmentFiber
