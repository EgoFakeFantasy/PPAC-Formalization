import PPAC.Migration.Internal.SyntaxTopEnvironmentFields
import PPAC.Migration.Internal.SyntaxMixedImageCodePairs

/-! 两类首槽环境的原自然列表码对；实际完整图见证保持在对象存在量词内。 -/
namespace PPAC.Migration.Internal.SyntaxTopCodedEnvironmentSyntax
open Source SourceAlgebra SourceLogic SyntaxRenameQuerySyntax

def instantiateState {m} (w a b A t R S f g : Fin m) : Formula m :=
  (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g).conj
    (SyntaxMixedImageCodeSyntax.encodings w f g A b a b R S)

def instantiateBody {m} (w a b A t R S : Fin m) : Formula (m+2) :=
  instantiateState w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def instantiateCoded {m} (w a b A t R S : Fin m) : Formula m := .ex (.ex (instantiateBody w a b A t R S))

def existsInstantiate {m} (w a b A t : Fin m) : Formula m := .ex (.ex
  (instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))

theorem instantiateState_rename {m k} (w a b A t R S f g : Fin m) (ρ : Fin m → Fin k) :
    (instantiateState w a b A t R S f g).rename ρ = instantiateState (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ R) (ρ S) (ρ f) (ρ g) := by
  simp only [instantiateState, Formula.rename, SyntaxTopEnvironmentSyntax.instantiateEnv_rename, SyntaxMixedImageCodeSyntax.encodings_rename]

theorem instantiateCoded_rename {m k} (w a b A t R S : Fin m) (ρ : Fin m → Fin k) :
    (instantiateCoded w a b A t R S).rename ρ = instantiateCoded (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ R) (ρ S) := by
  simp only [instantiateCoded, instantiateBody, Formula.rename, instantiateState_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsInstantiate_rename {m k} (w a b A t : Fin m) (ρ : Fin m → Fin k) :
    (existsInstantiate w a b A t).rename ρ = existsInstantiate (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) := by
  simp only [existsInstantiate, Formula.rename, instantiateCoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_instantiate {m} {Γ : Context m} (w a b A t R S f g : Fin m)
    (hh : Derives Γ (instantiateState w a b A t R S f g)) : Derives Γ (instantiateCoded w a b A t R S) := by
  apply Derives.exI f
  apply Derives.exI g
  exact of_eq (by simp only [instantiateBody, Formula.instantiate, instantiateState_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh

theorem intro_instantiate_pair {m} {Γ : Context m} (w a b A t R S : Fin m)
    (hh : Derives Γ (instantiateCoded w a b A t R S)) : Derives Γ (existsInstantiate w a b A t) := by
  apply Derives.exI R
  apply Derives.exI S
  exact of_eq (by simp only [Formula.instantiate, instantiateCoded_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh

def abstractState {m} (w a b A B R S f g : Fin m) : Formula m :=
  (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g).conj
    (SyntaxMixedImageCodeSyntax.encodings w f g a B A b R S)

def abstractBody {m} (w a b A B R S : Fin m) : Formula (m+2) :=
  abstractState w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def abstractCoded {m} (w a b A B R S : Fin m) : Formula m := .ex (.ex (abstractBody w a b A B R S))

def existsAbstract {m} (w a b A B : Fin m) : Formula m := .ex (.ex
  (abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))

theorem abstractState_rename {m k} (w a b A B R S f g : Fin m) (ρ : Fin m → Fin k) :
    (abstractState w a b A B R S f g).rename ρ = abstractState (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ R) (ρ S) (ρ f) (ρ g) := by
  simp only [abstractState, Formula.rename, SyntaxTopEnvironmentSyntax.abstractEnv_rename, SyntaxMixedImageCodeSyntax.encodings_rename]

theorem abstractCoded_rename {m k} (w a b A B R S : Fin m) (ρ : Fin m → Fin k) :
    (abstractCoded w a b A B R S).rename ρ = abstractCoded (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ R) (ρ S) := by
  simp only [abstractCoded, abstractBody, Formula.rename, abstractState_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsAbstract_rename {m k} (w a b A B : Fin m) (ρ : Fin m → Fin k) :
    (existsAbstract w a b A B).rename ρ = existsAbstract (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) := by
  simp only [existsAbstract, Formula.rename, abstractCoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_abstract {m} {Γ : Context m} (w a b A B R S f g : Fin m)
    (hh : Derives Γ (abstractState w a b A B R S f g)) : Derives Γ (abstractCoded w a b A B R S) := by
  apply Derives.exI f
  apply Derives.exI g
  exact of_eq (by simp only [abstractBody, Formula.instantiate, abstractState_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh

theorem intro_abstract_pair {m} {Γ : Context m} (w a b A B R S : Fin m)
    (hh : Derives Γ (abstractCoded w a b A B R S)) : Derives Γ (existsAbstract w a b A B) := by
  apply Derives.exI R
  apply Derives.exI S
  exact of_eq (by simp only [Formula.instantiate, abstractCoded_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh

end PPAC.Migration.Internal.SyntaxTopCodedEnvironmentSyntax
