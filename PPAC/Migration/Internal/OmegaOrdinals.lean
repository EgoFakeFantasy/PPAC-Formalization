import PPAC.Migration.Internal.ObjectCheckedSequences
import PPAC.Migration.ObjectOrdinalBasic

/-! 全部内部ω成员满足原完整序数定义；用于已证对象超限递归的自然数实例。 -/
namespace PPAC.Migration.Internal.OmegaOrdinals
open Source SourceAlgebra SourceLogic OmegaSyntax OrdinalSyntax

def matrix : Formula 1 := ordinal 0

theorem matrix_pred {m} (ρ : Fin 0 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = ordinal x := by
  simp only [MinimalPredicates.pred, matrix, ordinal_rename]
  change ordinal (Fin.lastCases x ρ (Fin.last 0)) = ordinal x
  rw [Fin.lastCases_last]

theorem base {m} {Γ : Context m} (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0)) :
    Derives Γ (OmegaInductionSyntax.base matrix (Fin.elim0 : Fin 0 → Fin m)) := by
  simp only [OmegaInductionSyntax.base, matrix_pred]
  apply Derives.allI
  have hf' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hf
  apply Derives.impI
  exact OrdinalEmpty.ordinal (Fin.last m) (add hf' _) (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (w : Fin m) (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0)) :
    Derives Γ (OmegaInductionSyntax.step matrix Fin.elim0 w) := by
  simp only [OmegaInductionSyntax.step, matrix_pred]
  apply Derives.allI
  apply Derives.allI
  have hf' : Derives (Context.image Formula.raise (Context.image Formula.raise Γ)) (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact OrdinalSuccessor.ordinal (Fin.last (m+1)) (Fin.last m).castSucc (add (add (add hf' _) _) _)
    (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))

theorem elements {m} {Γ : Context m} (w : Fin m)
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0)) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (ordinal (Fin.last m)))) := by
  have h := OmegaInduction.induction_on_omega matrix Fin.elim0 w hs hw (base hf) (step w hf)
  simpa only [OmegaInductionSyntax.holds, matrix_pred] using h

theorem at_member {m} {Γ : Context m} (w x : Fin m)
    (hh : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (ordinal (Fin.last m)))))
    (hx : Derives Γ (.mem x w)) : Derives Γ (ordinal x) := by
  have hi := Derives.allE x hh
  have hi' : Derives Γ ((Formula.mem x w).imp (ordinal x)) := by
    simpa only [Formula.instantiate, Formula.rename, ordinal_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact .impE hi' hx

def assumptions : Theory := fun q => q = Source.SetLanguage.foundation ∨ q = Source.SetLanguage.separation matrix

def sentence : Source.Sentence := ((omega (0 : Fin 1)).imp
  (.all ((Formula.mem (Fin.last 1) (0 : Fin 1).castSucc).imp (ordinal (Fin.last 1))))).close

theorem source_proof : Derives (assumptions.at 0) sentence := by
  apply close_derives
  apply Derives.impI
  have hf : Derives (assumptions.at 1) (Source.SetLanguage.foundation.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  have hs : Derives (assumptions.at 1) ((Source.SetLanguage.separation matrix).rename Fin.elim0) := .hyp ⟨_, Or.inr rfl, rfl⟩
  exact elements 0 (add hf _) (add hs _) (.hyp (Or.inl rfl))

theorem source_ZF_proof : Derives (Source.SetLanguage.ZF.at 0) sentence := by
  refine Derives.weaken ?_ source_proof
  rintro q ⟨s, hs, rfl⟩
  rcases hs with rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation matrix, rfl⟩

theorem kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence sentence) := TheoryTransport.sentence source_proof

theorem native_proof : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence sentence) := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := kernel_certificate)
  rintro q ⟨s, hs, rfl⟩
  rcases hs with rfl | rfl
  · exact ZFEquivalence.source_foundation
  · exact SeparationSyntax.source_separation matrix
end PPAC.Migration.Internal.OmegaOrdinals
