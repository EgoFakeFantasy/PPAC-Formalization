import PPAC.Migration.Internal.PacketAffineZero

/-! Actual affine fibers and exact invalid-candidate rejection, all in the object derivation kernel. -/
namespace PPAC.Migration.Internal.PacketAffineFiber
open Source SourceAlgebra SourceLogic OmegaSyntax PacketAffineSyntax PacketAffineCore
open SyntaxRenameQuerySyntax (of_eq)

theorem output_is_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d t n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d t n)) : Derives Γ (uniqueOutput w B d t n) := by
  apply Derives.allI
  apply Derives.impI
  let R := affine w.castSucc B.castSucc d.castSucc t.castSucc (Fin.last m)
  have hr : Derives (Context.add R (Context.image Formula.raise Γ)) R := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have ha1 := of_eq (affine_rename w B d t n Fin.castSucc) (under ha R)
  exact unique (ZFContext.under hZ R) w.castSucc B.castSucc d.castSucc t.castSucc (Fin.last m) n.castSucc hw1 hr ha1

theorem exists_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d t : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hd : Derives Γ (.mem d B)) (ht : Derives Γ (.mem t w)) :
    Derives Γ (fiber w B d t) := by
  let A := (Formula.mem (Fin.last m) w.castSucc).conj (affine w.castSucc B.castSucc d.castSucc t.castSucc (Fin.last m))
  let Δ := Context.add A (Context.image Formula.raise Γ)
  apply Derives.exE (p := A) (exists_value hZ w B d t hw hB hd ht)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw A)
  have hu := output_is_unique (ZFContext.under hZ A) w.castSucc B.castSucc d.castSucc t.castSucc (Fin.last m) hw1 (.conjR hA)
  have ho : Derives Δ (fiber w.castSucc B.castSucc d.castSucc t.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [A, Formula.instantiate, Formula.rename, affine_rename, uniqueOutput_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hA hu)
  exact of_eq (fiber_rename w B d t Fin.castSucc).symm ho

theorem reject_digit {m} {Γ : Context m} (w B d t n : Fin m) (hd : Derives Γ (Formula.mem d B).neg) :
    Derives Γ (affine w B d t n).neg := by
  apply Derives.impI
  exact .impE (add hd _) (digit_guard w B d t n (.hyp (Or.inl rfl)))

theorem reject_tail {m} {Γ : Context m} (w B d t n : Fin m) (ht : Derives Γ (Formula.mem t w).neg) :
    Derives Γ (affine w B d t n).neg := by
  apply Derives.impI
  exact .impE (add ht _) (tail_guard w B d t n (.hyp (Or.inl rfl)))

theorem reject_output {m} {Γ : Context m} (w B d t n : Fin m) (hn : Derives Γ (Formula.mem n w).neg) :
    Derives Γ (affine w B d t n).neg := by
  apply Derives.impI
  exact .impE (add hn _) (output_guard w B d t n (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketAffineFiber
