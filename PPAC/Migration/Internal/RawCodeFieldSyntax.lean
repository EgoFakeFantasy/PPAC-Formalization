import PPAC.Migration.Internal.RawCodeGetZero

/-! 原field为实际原始节点payload之后的get；中间载荷保持对象EX见证。 -/
namespace PPAC.Migration.Internal.RawCodeFieldSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax

def body {m} (w x i y p : Fin m) : Formula m :=
  (PairingProjectionSyntax.step true false w x p).conj (RawCodeGetSyntax.get w p i y)
def field {m} (w x i y : Fin m) : Formula m := .ex (body w.castSucc x.castSucc i.castSucc y.castSucc (Fin.last m))
def existsField {m} (w x i : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (field w.castSucc x.castSucc i.castSucc (Fin.last m)))
def fiber {m} (w x i : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (field w.castSucc x.castSucc i.castSucc (Fin.last m))).conj (.all
    ((field w.castSucc.castSucc x.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem body_rename {m l} (w x i y p : Fin m) (ρ : Fin m → Fin l) :
    (body w x i y p).rename ρ = body (ρ w) (ρ x) (ρ i) (ρ y) (ρ p) := by
  simp only [body, Formula.rename, PairingProjectionSyntax.step_rename, RawCodeGetSyntax.get_rename]

theorem field_rename {m l} (w x i y : Fin m) (ρ : Fin m → Fin l) :
    (field w x i y).rename ρ = field (ρ w) (ρ x) (ρ i) (ρ y) := by
  simp only [field, Formula.rename, body_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsField_rename {m l} (w x i : Fin m) (ρ : Fin m → Fin l) :
    (existsField w x i).rename ρ = existsField (ρ w) (ρ x) (ρ i) := by
  simp only [existsField, Formula.rename, field_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m l} (w x i : Fin m) (ρ : Fin m → Fin l) :
    (fiber w x i).rename ρ = fiber (ρ w) (ρ x) (ρ i) := by
  simp only [fiber, Formula.rename, field_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_field {m} {Γ : Context m} (w x i y p : Fin m)
    (hp : Derives Γ (PairingProjectionSyntax.step true false w x p)) (hy : Derives Γ (RawCodeGetSyntax.get w p i y)) : Derives Γ (field w x i y) := by
  have hb : Derives Γ (body w x i y p) := .conjI hp hy
  apply Derives.exI p
  simpa only [Formula.instantiate, body_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hb

theorem intro_exists {m} {Γ : Context m} (w x i y : Fin m) (hy : Derives Γ (.mem y w))
    (hf : Derives Γ (field w x i y)) : Derives Γ (existsField w x i) := by
  apply Derives.exI y
  simpa only [Formula.instantiate, Formula.rename, field_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hy hf

theorem get_input_subst {m} {Γ : Context m} (w a b i y : Fin m) (he : Derives Γ (.equal a b))
    (hy : Derives Γ (RawCodeGetSyntax.get w a i y)) : Derives Γ (RawCodeGetSyntax.get w b i y) := by
  have hi : Derives Γ ((RawCodeGetSyntax.get w.castSucc (Fin.last m) i.castSucc y.castSucc).instantiate a) := by
    simpa only [Formula.instantiate, RawCodeGetSyntax.get_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (RawCodeGetSyntax.get w.castSucc (Fin.last m) i.castSucc y.castSucc) he hi
  simpa only [Formula.instantiate, RawCodeGetSyntax.get_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

end PPAC.Migration.Internal.RawCodeFieldSyntax
