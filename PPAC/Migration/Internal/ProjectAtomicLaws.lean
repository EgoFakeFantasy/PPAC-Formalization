import PPAC.Migration.Internal.ProjectAtomicMember

/-! Three original atomic cases: exact pure types, unique outputs, primitive equality. -/
namespace PPAC.Migration.Internal.ProjectAtomicLaws
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectAtomicSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem bound_term {m} {Γ : Context m} (w b f x : Fin m) (hb : Derives Γ (.mem b w))
    (hf : Derives Γ (.mem f w)) (hx : Derives Γ (SyntaxTermSyntax.branch true w b x)) :
    Derives Γ (SyntaxTermSyntax.term w b f x) := .conjI (.conjI hb hf) (.disjL hx)

theorem result_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b z x y q r : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (result kind w b z x y q))
    (hr : Derives Γ (result kind w b z x y r)) : Derives Γ (.equal q r) := by
  rcases kind with ⟨k,hk⟩
  have h : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases h with rfl | rfl | rfl
  · exact ProjectAtomicMember.unique hZ w x y q r hw hq hr
  · exact SyntaxConstructors.unique hZ 2 3 w (SyntaxAtomSyntax.two x y) q r hw hq hr
  · exact ProjectSubsetLaws.unique hZ w b z x y q r hw hq hr

theorem result_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b z x y q : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hz : Derives Γ (empty z))
    (hx : Derives Γ (SyntaxTermSyntax.branch true w b x)) (hy : Derives Γ (SyntaxTermSyntax.branch true w b y))
    (hr : Derives Γ (result kind w b z x y q)) : Derives Γ (FormulaCodeSyntax.formulaCode w q b z) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hX := bound_term w b z x hb hzW hx
  have hY := bound_term w b z y hb hzW hy
  rcases kind with ⟨k,hk⟩
  have h : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases h with rfl | rfl | rfl
  · exact ProjectAtomicMember.target_type hZ w b z x y q hw hX hY hr
  · exact .impE (.conjR (FormulaCodeKnownAtomic.equal_iff hZ w b z x y q hw hr)) (.conjI hX hY)
  · exact ProjectSubsetLaws.target_type hZ w b z x y q hw hb hz hx hy hr

theorem compiled_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b z x y n q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (compiled kind w b z x y n q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w q b z) :=
  result_type hZ kind w b z x y q hw (.conjL (.conjL hc)) hz
    (.conjL (.conjR (.conjL hc))) (.conjL (.conjR (.conjR (.conjL hc)))) (.conjR hc)

theorem compiled_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b z x y n q r : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled kind w b z x y n q))
    (hr : Derives Γ (compiled kind w b z x y n r)) : Derives Γ (.equal q r) :=
  result_unique hZ kind w b z x y q r hw (.conjR hq) (.conjR hr)

theorem equal_same_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b z x y n q : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (compiled 1 w b z x y n q)) : Derives Γ (.equal q n) :=
  SyntaxConstructors.unique hZ 2 3 w (SyntaxAtomSyntax.two x y) q n hw (.conjR hc)
    (.conjR (.conjR (.conjR (.conjL hc))))

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b z x y n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled kind w b z x y n q)) :
    Derives Γ (uniqueOutput kind w b z x y n q) := by
  apply Derives.allI
  apply Derives.impI
  let E := compiled kind w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc n.castSucc (Fin.last m)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hq1 := of_eq (compiled_rename kind w b z x y n q Fin.castSucc) (under hq E)
  exact compiled_unique (ZFContext.under hZ E) kind w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc n.castSucc
    (Fin.last m) q.castSucc hw1 (.hyp (Or.inl rfl)) hq1

end PPAC.Migration.Internal.ProjectAtomicLaws
