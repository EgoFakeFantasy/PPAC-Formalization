import PPAC.Migration.Internal.ProofSubstitutionProjection
import PPAC.Migration.Internal.RawCodeFieldAtConstructor

/-! 实际前驱有限构造器的0／1字段与原投影查询对应；每个实例返回原核推导。 -/
namespace PPAC.Migration.Internal.ProofSubstitutionProjectionSlots
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax ProofSubstitutionProjectionSyntax
open SyntaxRenameQuerySyntax (of_eq)

def firstSlot (k : Nat) : Fin (k+2) := ⟨0, Nat.zero_lt_succ (k+1)⟩
def secondSlot (k : Nat) : Fin (k+2) := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ k)⟩

theorem free_at_constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (xs : Fin k → Fin m)
    (j : Fin k) (hj : j.val = 0) (w z : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hz : Derives Γ (empty z))
    (hp : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs (env 4))) :
    Derives Γ ((ProjectionExprQuery.query freeProjection w env).iff (.equal (env 2) (xs j))) := by
  have hz0 : Derives Γ (SyntaxNumeralSyntax.numeral j.val z) := by simpa only [hj, SyntaxNumeralSyntax.numeral] using hz
  exact SyntaxTypeLocalTransfer.iff_trans (ProofSubstitutionProjection.free_query_iff hZ w z env hw hn hz)
    (RawCodeFieldAtConstructor.constructor_at hZ k tag w xs (env 4) j z (env 2) hw hp hz0)

theorem formula_at_constructor_one {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (xs : Fin k → Fin m)
    (j : Fin k) (hj : j.val = 1) (w one : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (ho : Derives Γ (SyntaxNumeralSyntax.numeral 1 one))
    (hp : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs (env 4))) :
    Derives Γ ((ProjectionExprQuery.query formulaProjection w env).iff (.equal (env 5) (xs j))) := by
  have ho1 : Derives Γ (SyntaxNumeralSyntax.numeral j.val one) := by simpa only [hj] using ho
  exact SyntaxTypeLocalTransfer.iff_trans (ProofSubstitutionProjection.formula_query_at_one hZ w one env hw hn ho)
    (RawCodeFieldAtConstructor.constructor_at hZ k tag w xs (env 4) j one (env 5) hw hp ho1)

theorem formula_at_constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (xs : Fin k → Fin m)
    (j : Fin k) (hj : j.val = 1) (w : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env))
    (hp : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs (env 4))) :
    Derives Γ ((ProjectionExprQuery.query formulaProjection w env).iff (.equal (env 5) (xs j))) := by
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 1 (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxNumerals.exists_numeral hZ 1 w hw)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 := of_eq (environmentNat_rename 6 w env Fin.castSucc) (under hn B)
  have hp1 := of_eq (SyntaxNodeSyntax.constructor_rename k tag w xs (env 4) Fin.castSucc) (under hp B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := formula_at_constructor_one (ZFContext.under hZ B) k tag (fun v => (xs v).castSucc) j hj w.castSucc (Fin.last m)
    (fun v => (env v).castSucc) hw1 hn1 (.conjR hB) hp1
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, ProjectionExprQuery.query_rename]) ho

theorem projections_at_constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (xs : Fin k → Fin m)
    (j0 j1 : Fin k) (h0 : j0.val = 0) (h1 : j1.val = 1) (w z : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hz : Derives Γ (empty z))
    (hp : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs (env 4))) :
    Derives Γ ((projections w env).iff ((Formula.equal (env 2) (xs j0)).conj (.equal (env 5) (xs j1)))) :=
  FormulaCodeCongruence.conj_congr (free_at_constructor hZ k tag xs j0 h0 w z env hw hn hz hp)
    (formula_at_constructor hZ k tag xs j1 h1 w env hw hn hp)

end PPAC.Migration.Internal.ProofSubstitutionProjectionSlots
