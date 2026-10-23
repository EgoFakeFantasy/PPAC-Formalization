import PPAC.Migration.Internal.OriginalArgumentFieldUnique

/-! 原Run₂与全部内部字段像的完整双条件：反向由实际输出及字段码单射性取得。 -/
namespace PPAC.Migration.Internal.OriginalArgumentFieldCompletion
open Source SourceAlgebra SourceLogic OmegaSyntax
open OriginalArgumentFieldSyntax (fields fields_rename)
open SyntaxRenameQuerySyntax (of_eq)

def mapped {m} (w mode depth parameter k c d n q : Fin m) : Formula m :=
  (SyntaxMixedImageCodeSyntax.termList w k c d q).conj (fields w mode depth parameter k n q)

theorem mapped_rename {m j} (w mode depth parameter k c d n q : Fin m) (ρ : Fin m → Fin j) :
    (mapped w mode depth parameter k c d n q).rename ρ = mapped (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ k) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [mapped, Formula.rename, SyntaxMixedImageCodeSyntax.termList_rename, fields_rename]

theorem run_from_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool) (w mode depth parameter a b c d n k q : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hparam : Derives Γ (Formula.mem parameter w))
    (hpr : Derives Γ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    (hf : Derives Γ (OriginalArgumentValueSyntax.fiber w mode depth parameter k c d n))
    (hQ : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k c d q))
    (hF : Derives Γ (fields w mode depth parameter k n q))
    : Derives Γ (OriginalTransformRowSyntax.run 2 w mode depth parameter n q) := by
  let V := OriginalArgumentValueSyntax.value w.castSucc mode.castSucc depth.castSucc parameter.castSucc k.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE (p := V) hf
  have hZ1 := ZFContext.under hZ V
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [omega_rename]) (under hw V)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode.castSucc) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (under hm V)
  have hd1 : Derives Δ (Formula.mem depth.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (under hd V)
  have hparam1 : Derives Δ (Formula.mem parameter.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (under hparam V)
  have hpr1 : Derives Δ (OriginalNumericTermValueSyntax.promise w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc c.castSucc d.castSucc) := of_eq (by simp only [OriginalNumericTermValueSyntax.promise_rename]) (under hpr V)
  have hL1 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc k.castSucc a.castSucc b.castSucc n.castSucc) := of_eq (by simp only [SyntaxMixedImageCodeSyntax.termList_rename]) (under hL V)
  have hQ1 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc k.castSucc c.castSucc d.castSucc q.castSucc) := of_eq (by simp only [SyntaxMixedImageCodeSyntax.termList_rename]) (under hQ V)
  have hF1 : Derives Δ (fields w.castSucc mode.castSucc depth.castSucc parameter.castSucc k.castSucc n.castSucc q.castSucc) := of_eq (by simp only [fields_rename]) (under hF V)
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hFR := OriginalArgumentFieldInduction.actual_fields hZ1 three w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc n.castSucc k.castSucc (Fin.last m) hw1 hm1 hd1 hparam1 hL1 (.conjL hV)
  have he := OriginalArgumentFieldUnique.outputs_unique hZ1 w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc c.castSucc d.castSucc k.castSucc n.castSucc q.castSucc (Fin.last m) hw1 hL1 hpr1 hF1 hFR hQ1 (.conjL (.conjR hV))
  have ho := OriginalRunValueSubstitution.run_output 2 w.castSucc mode.castSucc depth.castSucc parameter.castSucc n.castSucc (Fin.last m) q.castSucc (eq_symm he) (.conjL hV)
  exact of_eq (OriginalTransformRowSyntax.run_rename 2 w mode depth parameter n q Fin.castSucc).symm ho

theorem run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool) (w mode depth parameter a b c d n k q : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hparam : Derives Γ (Formula.mem parameter w))
    (hc : Derives Γ (SyntaxTermSyntax.contexts w c d))
    (hpr : Derives Γ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    : Derives Γ ((OriginalTransformRowSyntax.run 2 w mode depth parameter n q).iff (mapped w mode depth parameter k c d n q)) := by
  have hf := OriginalArgumentValueInduction.actual_fiber hZ three w mode depth parameter a b c d n k hw hm hd hparam hc hpr hL
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalTransformRowSyntax.run 2 w mode depth parameter n q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hV := OriginalArgumentCandidateValue.at_run w mode depth parameter k c d n q (add hf E) hE
    have hF := OriginalArgumentFieldInduction.actual_fields (ZFContext.add hZ E) three w mode depth parameter a b n k q (add hw E) (add hm E) (add hd E) (add hparam E) (add hL E) hE
    exact .conjI (.conjL (.conjR hV)) hF
  · apply Derives.impI
    let E := mapped w mode depth parameter k c d n q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact run_from_fiber (ZFContext.add hZ E) three w mode depth parameter a b c d n k q (add hw E) (add hm E) (add hd E) (add hparam E) (add hpr E) (add hL E) (add hf E) (.conjL hE) (.conjR hE)

end PPAC.Migration.Internal.OriginalArgumentFieldCompletion
