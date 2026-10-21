import PPAC.Migration.Internal.GodelUnpairStep

/-! 编码值上的对象ω归纳给出全部内部自然码的实际解码。 -/
namespace PPAC.Migration.Internal.GodelUnpairExistence
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic GodelUnpairSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_preimage {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) : Derives Γ (preimage w z) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  exact intro_preimage w z z z hzW hzW (GodelUnpairTransitions.zero_code hZ w z hw hz)

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (OmegaInductionSyntax.base GodelUnpairSyntax.matrix (fun _ : Fin 1 => w)) := by
  simp only [OmegaInductionSyntax.base, GodelUnpairSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let Z := empty (Fin.last m)
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ Z
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Z
  exact zero_preimage hZ1 _ _ hw1 (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (OmegaInductionSyntax.step GodelUnpairSyntax.matrix (fun _ : Fin 1 => w) w) := by
  simp only [OmegaInductionSyntax.step, GodelUnpairSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hZ2 : ZFContext.Evidence Δ := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact GodelUnpairStep.successor_preimage (ZFContext.add (ZFContext.add (ZFContext.add hZ2 _) _) _) _ _ _
    (add (add (add hw2 _) _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem preimage_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w p : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w)) : Derives Γ (preimage w p) := by
  have hall := induction hZ GodelUnpairSyntax.matrix (fun _ : Fin 1 => w) w hw (base hZ w hw) (step hZ w hw)
  have hi : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (preimage w.castSucc (Fin.last m)))) := by
    simpa only [OmegaInductionSyntax.holds, GodelUnpairSyntax.matrix_pred, paramsUp] using hall
  have hi' : Derives Γ ((Formula.mem p w).imp (preimage w p)) := by
    simpa only [Formula.instantiate, Formula.rename, preimage_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE p hi
  exact .impE hi' hp
end PPAC.Migration.Internal.GodelUnpairExistence
