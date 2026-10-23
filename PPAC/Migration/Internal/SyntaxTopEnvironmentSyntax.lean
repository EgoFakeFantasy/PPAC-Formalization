import PPAC.Migration.Internal.SyntaxVariableTableFields
import PPAC.Migration.Internal.SyntaxMixedImageBinderAlign

/-! InstantiateTop/AbstractFreeTop的实际完整环境表合同；尚不等同原操作数值编码对应。 -/
namespace PPAC.Migration.Internal.SyntaxTopEnvironmentSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
open SyntaxVariableTableSyntax (identity identity_rename shifted shifted_rename)
open SyntaxTermImagePrefixSyntax (prefixed prefixed_rename)

def instantiateInput {m} (w a b A t : Fin m) : Formula m :=
  (SyntaxTermSyntax.term w a b t).conj (successor A a)

def abstractInput {m} (w a b A B : Fin m) : Formula m :=
  (SyntaxTermSyntax.contexts w a b).conj ((successor A a).conj (successor B b))

def instantiateData {m} (w a b A t f g u : Fin m) : Formula m :=
  (identity true w a b u).conj ((prefixed w u a a b t A f).conj (identity false w a b g))

def instantiateBody {m} (w a b A t f g : Fin m) : Formula (m+1) :=
  instantiateData w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc f.castSucc g.castSucc (Fin.last m)

def instantiateEnv {m} (w a b A t f g : Fin m) : Formula m := .ex (instantiateBody w a b A t f g)

def abstractData {m} (w a b A B f g u z n : Fin m) : Formula m :=
  (shifted true w a A b f).conj ((identity false w A b u).conj
    ((SyntaxMixedImageHead.head w A b z n).conj (prefixed w u b A b n B g)))

def abstractBody {m} (w a b A B f g : Fin m) : Formula (m+3) :=
  abstractData w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc
    A.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))

def abstractEnv {m} (w a b A B f g : Fin m) : Formula m := .ex (.ex (.ex (abstractBody w a b A B f g)))

theorem instantiateInput_rename {m k} (w a b A t : Fin m) (ρ : Fin m → Fin k) :
    (instantiateInput w a b A t).rename ρ = instantiateInput (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) := by
  simp only [instantiateInput, Formula.rename, SyntaxTermSyntax.term_rename, successor_rename]

theorem abstractInput_rename {m k} (w a b A B : Fin m) (ρ : Fin m → Fin k) :
    (abstractInput w a b A B).rename ρ = abstractInput (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) := by
  simp only [abstractInput, Formula.rename, SyntaxTermSyntax.contexts_rename, successor_rename]

theorem instantiateData_rename {m k} (w a b A t f g u : Fin m) (ρ : Fin m → Fin k) :
    (instantiateData w a b A t f g u).rename ρ = instantiateData (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ f) (ρ g) (ρ u) := by
  simp only [instantiateData, Formula.rename, identity_rename, prefixed_rename]

theorem instantiateEnv_rename {m k} (w a b A t f g : Fin m) (ρ : Fin m → Fin k) :
    (instantiateEnv w a b A t f g).rename ρ = instantiateEnv (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ f) (ρ g) := by
  simp only [instantiateEnv, instantiateBody, Formula.rename, instantiateData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem abstractData_rename {m k} (w a b A B f g u z n : Fin m) (ρ : Fin m → Fin k) :
    (abstractData w a b A B f g u z n).rename ρ = abstractData (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ f) (ρ g) (ρ u) (ρ z) (ρ n) := by
  simp only [abstractData, Formula.rename, shifted_rename, identity_rename, SyntaxMixedImageHead.head_rename, prefixed_rename]

theorem abstractEnv_rename {m k} (w a b A B f g : Fin m) (ρ : Fin m → Fin k) :
    (abstractEnv w a b A B f g).rename ρ = abstractEnv (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ f) (ρ g) := by
  simp only [abstractEnv, abstractBody, Formula.rename, abstractData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

def existsInstantiate {m} (w a b A t : Fin m) : Formula m := .ex (.ex
  (instantiateEnv w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))

theorem existsInstantiate_rename {m k} (w a b A t : Fin m) (ρ : Fin m → Fin k) :
    (existsInstantiate w a b A t).rename ρ = existsInstantiate (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) := by
  simp only [existsInstantiate, Formula.rename, instantiateEnv_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

def existsAbstract {m} (w a b A B : Fin m) : Formula m := .ex (.ex
  (abstractEnv w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))

theorem existsAbstract_rename {m k} (w a b A B : Fin m) (ρ : Fin m → Fin k) :
    (existsAbstract w a b A B).rename ρ = existsAbstract (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) := by
  simp only [existsAbstract, Formula.rename, abstractEnv_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_instantiate {m} {Γ : Context m} (w a b A t f g u : Fin m)
    (hh : Derives Γ (instantiateData w a b A t f g u)) : Derives Γ (instantiateEnv w a b A t f g) := by
  apply Derives.exI u
  exact of_eq (by simp only [instantiateBody, Formula.instantiate, instantiateData_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh

theorem intro_abstract {m} {Γ : Context m} (w a b A B f g u z n : Fin m)
    (hh : Derives Γ (abstractData w a b A B f g u z n)) : Derives Γ (abstractEnv w a b A B f g) := by
  apply Derives.exI u
  apply Derives.exI z
  apply Derives.exI n
  exact of_eq (by simp only [abstractBody, Formula.instantiate, abstractData_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh

theorem intro_instantiate_pair {m} {Γ : Context m} (w a b A t f g : Fin m)
    (hh : Derives Γ (instantiateEnv w a b A t f g)) : Derives Γ (existsInstantiate w a b A t) := by
  apply Derives.exI f
  apply Derives.exI g
  exact of_eq (by simp only [Formula.instantiate, instantiateEnv_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh

theorem intro_abstract_pair {m} {Γ : Context m} (w a b A B f g : Fin m)
    (hh : Derives Γ (abstractEnv w a b A B f g)) : Derives Γ (existsAbstract w a b A B) := by
  apply Derives.exI f
  apply Derives.exI g
  exact of_eq (by simp only [Formula.instantiate, abstractEnv_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh

theorem eliminate_abstract {m} {Γ : Context m} (w a b A B f g : Fin m) (P : Formula m)
    (he : Derives Γ (abstractEnv w a b A B f g))
    (hc : Derives (Context.add (abstractBody w a b A B f g)
      (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))) P.raise.raise.raise) : Derives Γ P := by
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨s1, ⟨s2, hs, h2⟩, h1⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨s1, Or.inr ⟨s2, Or.inr hs, h2⟩, h1⟩

end PPAC.Migration.Internal.SyntaxTopEnvironmentSyntax
