import PPAC.Migration.Internal.ObjectFormulaTransformProgram

/-! 原索引列表码到原变量项码列表的实际对象转换；所有图、码和元数据均内部绑定。 -/
namespace PPAC.Migration.Internal.IndexTermImageCodeSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def data {m} (isBound : Bool) (w I T a c d r f : Fin m) : Formula m :=
  (SyntaxMapCodeSyntax.encoded w r a (SyntaxTermSyntax.limit isBound c d) I).conj
    ((SyntaxVariableImageSyntax.mapped isBound w r a c d f).conj (SyntaxMixedImageCodeSyntax.encoded w f a c d T))

def body {m} (isBound : Bool) (w I T a c d : Fin m) : Formula (m+2) :=
  data isBound w.castSucc.castSucc I.castSucc.castSucc T.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def converted {m} (isBound : Bool) (w I T a c d : Fin m) : Formula m := .ex (.ex (body isBound w I T a c d))

def input {m} (isBound : Bool) (w I a c d : Fin m) : Formula m :=
  (SyntaxTermSyntax.contexts w c d).conj (SyntaxMapCodeSyntax.mapCode w a (SyntaxTermSyntax.limit isBound c d) I)

def atGraph {m} (isBound : Bool) (w r T a c d : Fin m) : Formula m := .ex
  ((SyntaxVariableImageSyntax.mapped isBound w.castSucc r.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m)).conj
    (SyntaxMixedImageCodeSyntax.encoded w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc T.castSucc))

def existsCode {m} (isBound : Bool) (w I a c d : Fin m) : Formula m := .ex
  (converted isBound w.castSucc I.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc)

def uniqueCode {m} (isBound : Bool) (w I T a c d : Fin m) : Formula m := .all
  ((converted isBound w.castSucc I.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc).imp (.equal (Fin.last m) T.castSucc))

def fiber {m} (isBound : Bool) (w I a c d : Fin m) : Formula m := .ex
  ((converted isBound w.castSucc I.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc).conj
    (uniqueCode isBound w.castSucc I.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc))

def environment {m} (w I J R S a b c d : Fin m) : Formula m :=
  (converted true w I R a c d).conj (converted false w J S b c d)

def existsEnvironment {m} (w I J a b c d : Fin m) : Formula m := .ex (.ex
  (environment w.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc))

theorem data_rename {m k} (isBound : Bool) (w I T a c d r f : Fin m) (ρ : Fin m → Fin k) :
    (data isBound w I T a c d r f).rename ρ = data isBound (ρ w) (ρ I) (ρ T) (ρ a) (ρ c) (ρ d) (ρ r) (ρ f) := by
  simp only [data, Formula.rename, SyntaxMapCodeSyntax.encoded_rename, SyntaxTermSyntax.limit_map, SyntaxVariableImageSyntax.mapped_rename, SyntaxMixedImageCodeSyntax.encoded_rename]

theorem converted_rename {m k} (isBound : Bool) (w I T a c d : Fin m) (ρ : Fin m → Fin k) :
    (converted isBound w I T a c d).rename ρ = converted isBound (ρ w) (ρ I) (ρ T) (ρ a) (ρ c) (ρ d) := by
  simp only [converted, body, Formula.rename, data_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem input_rename {m k} (isBound : Bool) (w I a c d : Fin m) (ρ : Fin m → Fin k) :
    (input isBound w I a c d).rename ρ = input isBound (ρ w) (ρ I) (ρ a) (ρ c) (ρ d) := by
  simp only [input, Formula.rename, SyntaxTermSyntax.contexts_rename, SyntaxMapCodeSyntax.mapCode_rename, SyntaxTermSyntax.limit_map]

theorem atGraph_rename {m k} (isBound : Bool) (w r T a c d : Fin m) (ρ : Fin m → Fin k) :
    (atGraph isBound w r T a c d).rename ρ = atGraph isBound (ρ w) (ρ r) (ρ T) (ρ a) (ρ c) (ρ d) := by
  simp only [atGraph, Formula.rename, SyntaxVariableImageSyntax.mapped_rename, SyntaxMixedImageCodeSyntax.encoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsCode_rename {m k} (isBound : Bool) (w I a c d : Fin m) (ρ : Fin m → Fin k) :
    (existsCode isBound w I a c d).rename ρ = existsCode isBound (ρ w) (ρ I) (ρ a) (ρ c) (ρ d) := by
  simp only [existsCode, Formula.rename, converted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueCode_rename {m k} (isBound : Bool) (w I T a c d : Fin m) (ρ : Fin m → Fin k) :
    (uniqueCode isBound w I T a c d).rename ρ = uniqueCode isBound (ρ w) (ρ I) (ρ T) (ρ a) (ρ c) (ρ d) := by
  simp only [uniqueCode, Formula.rename, converted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k} (isBound : Bool) (w I a c d : Fin m) (ρ : Fin m → Fin k) :
    (fiber isBound w I a c d).rename ρ = fiber isBound (ρ w) (ρ I) (ρ a) (ρ c) (ρ d) := by
  simp only [fiber, Formula.rename, converted_rename, uniqueCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem environment_rename {m k} (w I J R S a b c d : Fin m) (ρ : Fin m → Fin k) :
    (environment w I J R S a b c d).rename ρ = environment (ρ w) (ρ I) (ρ J) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) := by
  simp only [environment, Formula.rename, converted_rename]

theorem existsEnvironment_rename {m k} (w I J a b c d : Fin m) (ρ : Fin m → Fin k) :
    (existsEnvironment w I J a b c d).rename ρ = existsEnvironment (ρ w) (ρ I) (ρ J) (ρ a) (ρ b) (ρ c) (ρ d) := by
  simp only [existsEnvironment, Formula.rename, environment_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_converted {m} {Γ : Context m} (isBound : Bool) (w I T a c d r f : Fin m)
    (hd : Derives Γ (data isBound w I T a c d r f)) : Derives Γ (converted isBound w I T a c d) := by
  apply Derives.exI r
  apply Derives.exI f
  exact of_eq (by simp only [body, Formula.instantiate, data_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hd

theorem intro_atGraph {m} {Γ : Context m} (isBound : Bool) (w r T a c d f : Fin m)
    (hm : Derives Γ (SyntaxVariableImageSyntax.mapped isBound w r a c d f))
    (he : Derives Γ (SyntaxMixedImageCodeSyntax.encoded w f a c d T)) : Derives Γ (atGraph isBound w r T a c d) := by
  apply Derives.exI f
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxVariableImageSyntax.mapped_rename, SyntaxMixedImageCodeSyntax.encoded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hm he)

theorem intro_exists {m} {Γ : Context m} (isBound : Bool) (w I T a c d : Fin m)
    (hc : Derives Γ (converted isBound w I T a c d)) : Derives Γ (existsCode isBound w I a c d) := by
  apply Derives.exI T
  exact of_eq (by simp only [Formula.instantiate, converted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc

theorem intro_fiber {m} {Γ : Context m} (isBound : Bool) (w I T a c d : Fin m)
    (hc : Derives Γ (converted isBound w I T a c d)) (hu : Derives Γ (uniqueCode isBound w I T a c d)) : Derives Γ (fiber isBound w I a c d) := by
  apply Derives.exI T
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, converted_rename, uniqueCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hc hu)

theorem intro_environment {m} {Γ : Context m} (w I J R S a b c d : Fin m)
    (he : Derives Γ (environment w I J R S a b c d)) : Derives Γ (existsEnvironment w I J a b c d) := by
  apply Derives.exI R
  apply Derives.exI S
  exact of_eq (by simp only [Formula.instantiate, environment_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) he

end PPAC.Migration.Internal.IndexTermImageCodeSyntax
