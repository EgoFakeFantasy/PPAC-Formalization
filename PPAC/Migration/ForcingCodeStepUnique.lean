import PPAC.Migration.ForcingCodeTotal
import PPAC.Migration.Internal.FormulaCodeCaseLogic

/-! Determinism of the concrete pinned forcing-code dispatch. The only extra
premise is an object formula asserting functionality of earlier history reads.
The following recursive-uniqueness consumer must discharge that premise by
internal code induction; this module alone is not global uniqueness or Con.
All witnesses are internal, and no output is selected in Lean. -/
namespace PPAC.Migration.ForcingCodeStepUnique
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
set_option maxRecDepth 16384

/-- Functionality of every earlier read, for arbitrary internal bound scope. -/
def functional {m} (w f h n : Fin m) : Formula m := .all (.all (.all (.all
  ((Formula.mem (Fin.last m).castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc).imp
    ((ForcingCodeStep.read w.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc).imp
    ((ForcingCodeStep.read w.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3))).imp
      (.equal (Fin.last (m+2)).castSucc (Fin.last (m+3)))))))))

theorem functional_rename {m l} (w f h n : Fin m) (r : Fin m → Fin l) :
    (functional w f h n).rename r = functional (r w) (r f) (r h) (r n) := by
  simp only [functional, Formula.rename, ForcingCodeStep.read_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem functional_at {m} {Γ : Context m} (w f h n x a Q V : Fin m)
    (hf : Derives Γ (functional w f h n)) (hx : Derives Γ (.mem x n))
    (hq : Derives Γ (ForcingCodeStep.read w h x a f Q)) (hv : Derives Γ (ForcingCodeStep.read w h x a f V)) :
    Derives Γ (.equal Q V) := by
  have hi : Derives Γ ((Formula.mem x n).imp ((ForcingCodeStep.read w h x a f Q).imp
      ((ForcingCodeStep.read w h x a f V).imp (.equal Q V)))) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, ForcingCodeStep.read_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.allE V (Derives.allE Q (Derives.allE a (Derives.allE x hf))))
  exact .impE (.impE (.impE hi hx) hq) hv

private theorem read_source_subst {m} {Γ : Context m} (w h x a f Q y : Fin m)
    (he : Derives Γ (.equal x y)) (hr : Derives Γ (ForcingCodeStep.read w h x a f Q)) :
    Derives Γ (ForcingCodeStep.read w h y a f Q) := by
  let P := ForcingCodeStep.read w.castSucc h.castSucc (Fin.last m) a.castSucc f.castSucc Q.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, ForcingCodeStep.read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, ForcingCodeStep.read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr))
private def negativeData {k m} (R : Source.Formula (k+2)) (_H : Source.Formula (k+1)) (w z f j a A _B _C h n Q x X : Fin m) : Formula m :=
  (FormulaCodeRecursiveSyntax.singleFields 4 false w a z x n).conj
    ((ForcingCodeStep.read w h x a f X).conj (ForcingNegCode.compiled R w a A f j X Q))
private theorem negativeData_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x X : Fin m) (r : Fin m → Fin l) :
    (negativeData R H w z f j a A B C h n Q x X).rename r = negativeData R H (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r h) (r n) (r Q) (r x) (r X) := by
  simp only [negativeData, Formula.rename, FormulaCodeRecursiveSyntax.singleFields_rename, ForcingCodeStep.read_rename, ForcingNegCode.compiled_rename R]
private def negativeBody {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) : Formula (m+2) :=
  negativeData R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 Q) (slot 2 0) (slot 2 1)

private theorem negative_data_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V x X u U : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (h1 : Derives Γ (negativeData R H w z f j a A B C h n Q x X)) (h2 : Derives Γ (negativeData R H w z f j a A B C h n V u U)) : Derives Γ (.equal Q V) := by
  have eu := SyntaxLogicalFields.single_fields hZ 4 w u x n hw (.conjL (.conjL h2)) (.conjL (.conjL h1))
  have hu := read_source_subst w h u a f U x eu (.conjL (.conjR h2))
  have eU := functional_at w f h n x a U X hf (.conjL (.conjR (.conjL h1))) hu (.conjL (.conjR h1))
  let P := ForcingNegCode.compiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc (Fin.last m) V.castSucc
  have hq : Derives Γ (ForcingNegCode.compiled R w a A f j X Q) := .conjR (.conjR h1)
  have hv : Derives Γ (ForcingNegCode.compiled R w a A f j X V) :=
    of_eq (by simp only [P, Formula.instantiate, ForcingNegCode.compiled_rename R, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P eU (of_eq (by simp only [P, Formula.instantiate, ForcingNegCode.compiled_rename R, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR (.conjR h2))))
  exact ForcingNegCode.unique hZ R w a A f j X Q V hw hq hv

private theorem negative_at_data_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V x X : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (h1 : Derives Γ (negativeData R H w z f j a A B C h n Q x X))
    (h2 : Derives Γ (ForcingCodeStep.negative R H w z f j a A B C h n V)) : Derives Γ (.equal Q V) := by
  let T := negativeBody R H w z f j a A B C h n V
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ h2
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact negative_data_unique (HornBinderRules.zf_body 2 hZ T) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 Q) (old 2 V) (old 2 x) (old 2 X) (slot 2 0) (slot 2 1)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T))
    (of_eq (functional_rename w f h n (old 2)) (HornBinderRules.under_body 2 hf T))
    (of_eq (negativeData_rename R H w z f j a A B C h n Q x X (old 2)) (HornBinderRules.under_body 2 h1 T)) hT

private theorem negative_reject {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (arity label : Nat) (hne : label ≠ 4)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor arity label w xs n))
    (hb : Derives Γ (ForcingCodeStep.negative R H w z f j a A B C h n Q)) : Derives Γ .bot := by
  let T := negativeBody R H w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hb
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint (HornBinderRules.zf_body 2 hZ T) arity 1 label 4 hne
    (old 2 w) (fun i => old 2 (xs i)) (fun _ => slot 2 0) (old 2 n)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T))
    (of_eq (SyntaxNodeSyntax.constructor_rename arity label w xs n (old 2)) (HornBinderRules.under_body 2 hc T)) (.conjL (.conjL hT))

private theorem negative_atomic_reject {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (SyntaxAtomSyntax.atomic w a z n))
    (hb : Derives Γ (ForcingCodeStep.negative R H w z f j a A B C h n Q)) : Derives Γ .bot := by
  let T := negativeBody R H w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hb
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact FormulaCodeCaseLogic.atomic_conflict (HornBinderRules.zf_body 2 hZ T) 1 4
    (by decide) (by decide) (by decide) (by decide) (old 2 w) (old 2 a) (old 2 z) (old 2 n) (fun _ => slot 2 0)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T)) (.conjL (.conjL hT))
    (of_eq (SyntaxAtomSyntax.atomic_rename w a z n (old 2)) (HornBinderRules.under_body 2 ha T))
private def universalData {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x X : Fin m) : Formula m :=
  (FormulaCodeRecursiveSyntax.singleFields 9 true w a z x n).conj
    ((ForcingCodeStep.read w h x A f X).conj (ForcingLogicalCode.universal R H w a A B C f j X Q))
private theorem universalData_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x X : Fin m) (r : Fin m → Fin l) :
    (universalData R H w z f j a A B C h n Q x X).rename r = universalData R H (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r h) (r n) (r Q) (r x) (r X) := by
  simp only [universalData, Formula.rename, FormulaCodeRecursiveSyntax.singleFields_rename, ForcingCodeStep.read_rename, ForcingLogicalCode.universal_rename R H]
private def universalBody {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) : Formula (m+2) :=
  universalData R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 Q) (slot 2 0) (slot 2 1)

private theorem universal_data_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V x X u U : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (h1 : Derives Γ (universalData R H w z f j a A B C h n Q x X)) (h2 : Derives Γ (universalData R H w z f j a A B C h n V u U)) : Derives Γ (.equal Q V) := by
  have eu := SyntaxLogicalFields.single_fields hZ 9 w u x n hw (.conjL (.conjL h2)) (.conjL (.conjL h1))
  have hu := read_source_subst w h u A f U x eu (.conjL (.conjR h2))
  have eU := functional_at w f h n x A U X hf (.conjL (.conjR (.conjL h1))) hu (.conjL (.conjR h1))
  let P := ForcingLogicalCode.universal R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc (Fin.last m) V.castSucc
  have hq : Derives Γ (ForcingLogicalCode.universal R H w a A B C f j X Q) := .conjR (.conjR h1)
  have hv : Derives Γ (ForcingLogicalCode.universal R H w a A B C f j X V) :=
    of_eq (by simp only [P, Formula.instantiate, ForcingLogicalCode.universal_rename R H, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P eU (of_eq (by simp only [P, Formula.instantiate, ForcingLogicalCode.universal_rename R H, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR (.conjR h2))))
  exact ForcingLogicalCode.universal_unique hZ R H w a A B C f j X Q V hw hq hv

private theorem universal_at_data_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V x X : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (h1 : Derives Γ (universalData R H w z f j a A B C h n Q x X))
    (h2 : Derives Γ (ForcingCodeStep.universal R H w z f j a A B C h n V)) : Derives Γ (.equal Q V) := by
  let T := universalBody R H w z f j a A B C h n V
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ h2
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact universal_data_unique (HornBinderRules.zf_body 2 hZ T) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 Q) (old 2 V) (old 2 x) (old 2 X) (slot 2 0) (slot 2 1)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T))
    (of_eq (functional_rename w f h n (old 2)) (HornBinderRules.under_body 2 hf T))
    (of_eq (universalData_rename R H w z f j a A B C h n Q x X (old 2)) (HornBinderRules.under_body 2 h1 T)) hT

private theorem universal_reject {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (arity label : Nat) (hne : label ≠ 9)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor arity label w xs n))
    (hb : Derives Γ (ForcingCodeStep.universal R H w z f j a A B C h n Q)) : Derives Γ .bot := by
  let T := universalBody R H w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hb
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint (HornBinderRules.zf_body 2 hZ T) arity 1 label 9 hne
    (old 2 w) (fun i => old 2 (xs i)) (fun _ => slot 2 0) (old 2 n)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T))
    (of_eq (SyntaxNodeSyntax.constructor_rename arity label w xs n (old 2)) (HornBinderRules.under_body 2 hc T)) (.conjL (.conjL hT))

private theorem universal_atomic_reject {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (SyntaxAtomSyntax.atomic w a z n))
    (hb : Derives Γ (ForcingCodeStep.universal R H w z f j a A B C h n Q)) : Derives Γ .bot := by
  let T := universalBody R H w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hb
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact FormulaCodeCaseLogic.atomic_conflict (HornBinderRules.zf_body 2 hZ T) 1 9
    (by decide) (by decide) (by decide) (by decide) (old 2 w) (old 2 a) (old 2 z) (old 2 n) (fun _ => slot 2 0)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T)) (.conjL (.conjL hT))
    (of_eq (SyntaxAtomSyntax.atomic_rename w a z n (old 2)) (HornBinderRules.under_body 2 ha T))
private def existentialData {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x X : Fin m) : Formula m :=
  (FormulaCodeRecursiveSyntax.singleFields 10 true w a z x n).conj
    ((ForcingCodeStep.read w h x A f X).conj (ForcingExistCode.compiled R H w a A B C f j X Q))
private theorem existentialData_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x X : Fin m) (r : Fin m → Fin l) :
    (existentialData R H w z f j a A B C h n Q x X).rename r = existentialData R H (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r h) (r n) (r Q) (r x) (r X) := by
  simp only [existentialData, Formula.rename, FormulaCodeRecursiveSyntax.singleFields_rename, ForcingCodeStep.read_rename, ForcingExistCode.compiled_rename R H]
private def existentialBody {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) : Formula (m+2) :=
  existentialData R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 Q) (slot 2 0) (slot 2 1)

private theorem existential_data_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V x X u U : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (h1 : Derives Γ (existentialData R H w z f j a A B C h n Q x X)) (h2 : Derives Γ (existentialData R H w z f j a A B C h n V u U)) : Derives Γ (.equal Q V) := by
  have eu := SyntaxLogicalFields.single_fields hZ 10 w u x n hw (.conjL (.conjL h2)) (.conjL (.conjL h1))
  have hu := read_source_subst w h u A f U x eu (.conjL (.conjR h2))
  have eU := functional_at w f h n x A U X hf (.conjL (.conjR (.conjL h1))) hu (.conjL (.conjR h1))
  let P := ForcingExistCode.compiled R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc (Fin.last m) V.castSucc
  have hq : Derives Γ (ForcingExistCode.compiled R H w a A B C f j X Q) := .conjR (.conjR h1)
  have hv : Derives Γ (ForcingExistCode.compiled R H w a A B C f j X V) :=
    of_eq (by simp only [P, Formula.instantiate, ForcingExistCode.compiled_rename R H, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P eU (of_eq (by simp only [P, Formula.instantiate, ForcingExistCode.compiled_rename R H, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR (.conjR h2))))
  exact ForcingExistCode.unique hZ R H w a A B C f j X Q V hw hq hv

private theorem existential_at_data_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V x X : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (h1 : Derives Γ (existentialData R H w z f j a A B C h n Q x X))
    (h2 : Derives Γ (ForcingCodeStep.existential R H w z f j a A B C h n V)) : Derives Γ (.equal Q V) := by
  let T := existentialBody R H w z f j a A B C h n V
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ h2
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact existential_data_unique (HornBinderRules.zf_body 2 hZ T) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 Q) (old 2 V) (old 2 x) (old 2 X) (slot 2 0) (slot 2 1)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T))
    (of_eq (functional_rename w f h n (old 2)) (HornBinderRules.under_body 2 hf T))
    (of_eq (existentialData_rename R H w z f j a A B C h n Q x X (old 2)) (HornBinderRules.under_body 2 h1 T)) hT

private theorem existential_reject {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (arity label : Nat) (hne : label ≠ 10)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor arity label w xs n))
    (hb : Derives Γ (ForcingCodeStep.existential R H w z f j a A B C h n Q)) : Derives Γ .bot := by
  let T := existentialBody R H w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hb
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint (HornBinderRules.zf_body 2 hZ T) arity 1 label 10 hne
    (old 2 w) (fun i => old 2 (xs i)) (fun _ => slot 2 0) (old 2 n)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T))
    (of_eq (SyntaxNodeSyntax.constructor_rename arity label w xs n (old 2)) (HornBinderRules.under_body 2 hc T)) (.conjL (.conjL hT))

private theorem existential_atomic_reject {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (SyntaxAtomSyntax.atomic w a z n))
    (hb : Derives Γ (ForcingCodeStep.existential R H w z f j a A B C h n Q)) : Derives Γ .bot := by
  let T := existentialBody R H w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hb
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact FormulaCodeCaseLogic.atomic_conflict (HornBinderRules.zf_body 2 hZ T) 1 10
    (by decide) (by decide) (by decide) (by decide) (old 2 w) (old 2 a) (old 2 z) (old 2 n) (fun _ => slot 2 0)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T)) (.conjL (.conjL hT))
    (of_eq (SyntaxAtomSyntax.atomic_rename w a z n (old 2)) (HornBinderRules.under_body 2 ha T))
private def binaryBody {k m} (kind : Fin 4) (R : Source.Formula (k+2)) (w z f j a A B C h n Q : Fin m) : Formula (m+4) :=
  ForcingCodeStep.binaryData kind R (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 h) (old 4 n) (old 4 Q) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)

private theorem binary_data_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (R : Source.Formula (k+2)) (w z f j a A B C h n Q V x y X Y u t U W : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (h1 : Derives Γ (ForcingCodeStep.binaryData kind R w z f j a A B C h n Q x y X Y))
    (h2 : Derives Γ (ForcingCodeStep.binaryData kind R w z f j a A B C h n V u t U W)) : Derives Γ (.equal Q V) := by
  have eu := SyntaxLogicalFields.binary_fields hZ kind w u t x y n hw (.conjL (.conjL h2)) (.conjL (.conjL h1))
  have hu := read_source_subst w h u a f U x (.conjL eu) (.conjL (.conjR h2))
  have ht := read_source_subst w h t a f W y (.conjR eu) (.conjL (.conjR (.conjR h2)))
  have eU := functional_at w f h n x a U X hf (.conjL (.conjR (.conjL h1))) hu (.conjL (.conjR h1))
  have eW := functional_at w f h n y a W Y hf (.conjL (.conjR (.conjR (.conjL h1)))) ht (.conjL (.conjR (.conjR h1)))
  let P := ForcingLogicalCode.binary kind R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc (Fin.last m) W.castSucc V.castSucc
  have h0 : Derives Γ (ForcingLogicalCode.binary kind R w a A f j X W V) :=
    of_eq (by simp only [P, Formula.instantiate, ForcingLogicalCode.binary_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P eU (of_eq (by simp only [P, Formula.instantiate, ForcingLogicalCode.binary_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR (.conjR (.conjR h2)))))
  let S := ForcingLogicalCode.binary kind R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc X.castSucc (Fin.last m) V.castSucc
  have hv : Derives Γ (ForcingLogicalCode.binary kind R w a A f j X Y V) :=
    of_eq (by simp only [S, Formula.instantiate, ForcingLogicalCode.binary_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst S eW (of_eq (by simp only [S, Formula.instantiate, ForcingLogicalCode.binary_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h0))
  exact ForcingLogicalCode.binary_unique hZ kind R w a A f j X Y Q V hw (.conjR (.conjR (.conjR h1))) hv

private theorem binary_at_data_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (R : Source.Formula (k+2)) (w z f j a A B C h n Q V x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (h1 : Derives Γ (ForcingCodeStep.binaryData kind R w z f j a A B C h n Q x y X Y))
    (h2 : Derives Γ (ForcingCodeStep.binary kind R w z f j a A B C h n V)) : Derives Γ (.equal Q V) := by
  let T := binaryBody kind R w z f j a A B C h n V
  let Δ := Context.add T (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 T _ h2
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact binary_data_unique (HornBinderRules.zf_body 4 hZ T) kind R (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 h) (old 4 n) (old 4 Q) (old 4 V) (old 4 x) (old 4 y) (old 4 X) (old 4 Y) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
    (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw T))
    (of_eq (functional_rename w f h n (old 4)) (HornBinderRules.under_body 4 hf T))
    (of_eq (ForcingCodeStep.binaryData_rename kind R w z f j a A B C h n Q x y X Y (old 4)) (HornBinderRules.under_body 4 h1 T)) hT

private theorem binary_reject {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (arity label : Nat) (hne : label ≠ SyntaxLogicalSyntax.binaryTag kind)
    (R : Source.Formula (k+2)) (w z f j a A B C h n Q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor arity label w xs n))
    (hb : Derives Γ (ForcingCodeStep.binary kind R w z f j a A B C h n Q)) : Derives Γ .bot := by
  let T := binaryBody kind R w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 T _ hb
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint (HornBinderRules.zf_body 4 hZ T) arity 2 label (SyntaxLogicalSyntax.binaryTag kind) hne
    (old 4 w) (fun i => old 4 (xs i)) (SyntaxAtomSyntax.two (slot 4 0) (slot 4 1)) (old 4 n)
    (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw T))
    (of_eq (SyntaxNodeSyntax.constructor_rename arity label w xs n (old 4)) (HornBinderRules.under_body 4 hc T)) (.conjL (.conjL hT))

private theorem binary_atomic_reject {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (R : Source.Formula (k+2)) (w z f j a A B C h n Q : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (SyntaxAtomSyntax.atomic w a z n))
    (hb : Derives Γ (ForcingCodeStep.binary kind R w z f j a A B C h n Q)) : Derives Γ .bot := by
  let T := binaryBody kind R w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 T _ hb
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0 : SyntaxLogicalSyntax.binaryTag kind ≠ 0 := (by exact (show ∀ i : Fin 4, SyntaxLogicalSyntax.binaryTag i ≠ 0 by decide) kind)
  have h1 : SyntaxLogicalSyntax.binaryTag kind ≠ 1 := (by exact (show ∀ i : Fin 4, SyntaxLogicalSyntax.binaryTag i ≠ 1 by decide) kind)
  have h2 : SyntaxLogicalSyntax.binaryTag kind ≠ 2 := (by exact (show ∀ i : Fin 4, SyntaxLogicalSyntax.binaryTag i ≠ 2 by decide) kind)
  have h3 : SyntaxLogicalSyntax.binaryTag kind ≠ 3 := (by exact (show ∀ i : Fin 4, SyntaxLogicalSyntax.binaryTag i ≠ 3 by decide) kind)
  exact FormulaCodeCaseLogic.atomic_conflict (HornBinderRules.zf_body 4 hZ T) 2 (SyntaxLogicalSyntax.binaryTag kind) h0 h1 h2 h3
    (old 4 w) (old 4 a) (old 4 z) (old 4 n) (SyntaxAtomSyntax.two (slot 4 0) (slot 4 1))
    (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw T)) (.conjL (.conjL hT))
    (of_eq (SyntaxAtomSyntax.atomic_rename w a z n (old 4)) (HornBinderRules.under_body 4 ha T))
private theorem select_atomic {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxAtomSyntax.atomic w a z n))
    (hs : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n Q)) : Derives Γ ((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q)) := by
  have h_atomic : Derives Γ (((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q)).imp ((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q))) := by
    apply Derives.impI
    exact .hyp (Or.inl rfl)
  have h_negative : Derives Γ ((ForcingCodeStep.negative R H w z f j a A B C h n Q).imp ((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q))) := by
    apply Derives.impI
    exact .botE (negative_atomic_reject (ZFContext.add hZ _) R H w z f j a A B C h n Q (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b0 : Derives Γ ((ForcingCodeStep.binary 0 R w z f j a A B C h n Q).imp ((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q))) := by
    apply Derives.impI
    exact .botE (binary_atomic_reject (ZFContext.add hZ _) 0 R w z f j a A B C h n Q (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b1 : Derives Γ ((ForcingCodeStep.binary 1 R w z f j a A B C h n Q).imp ((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q))) := by
    apply Derives.impI
    exact .botE (binary_atomic_reject (ZFContext.add hZ _) 1 R w z f j a A B C h n Q (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b2 : Derives Γ ((ForcingCodeStep.binary 2 R w z f j a A B C h n Q).imp ((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q))) := by
    apply Derives.impI
    exact .botE (binary_atomic_reject (ZFContext.add hZ _) 2 R w z f j a A B C h n Q (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b3 : Derives Γ ((ForcingCodeStep.binary 3 R w z f j a A B C h n Q).imp ((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q))) := by
    apply Derives.impI
    exact .botE (binary_atomic_reject (ZFContext.add hZ _) 3 R w z f j a A B C h n Q (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_universal : Derives Γ ((ForcingCodeStep.universal R H w z f j a A B C h n Q).imp ((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q))) := by
    apply Derives.impI
    exact .botE (universal_atomic_reject (ZFContext.add hZ _) R H w z f j a A B C h n Q (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_existential : Derives Γ ((ForcingCodeStep.existential R H w z f j a A B C h n Q).imp ((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q))) := by
    apply Derives.impI
    exact .botE (existential_atomic_reject (ZFContext.add hZ _) R H w z f j a A B C h n Q (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  exact .impE (FormulaCodeCaseLogic.disj_imp h_atomic (FormulaCodeCaseLogic.disj_imp h_negative (FormulaCodeCaseLogic.disj_imp h_b0 (FormulaCodeCaseLogic.disj_imp h_b1 (FormulaCodeCaseLogic.disj_imp h_b2 (FormulaCodeCaseLogic.disj_imp h_b3 (FormulaCodeCaseLogic.disj_imp h_universal h_existential))))))) hs

private theorem select_negative {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 1 4 w (fun _ => x) n))
    (hs : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n Q)) : Derives Γ (ForcingCodeStep.negative R H w z f j a A B C h n Q) := by
  have h_atomic : Derives Γ (((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q)).imp (ForcingCodeStep.negative R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (FormulaCodeCaseLogic.atomic_conflict (ZFContext.add hZ _) 1 4 (by decide) (by decide) (by decide) (by decide) w a z n (fun _ => x) (add hw _) (add hc _) (.conjL (.hyp (Or.inl rfl))))
  have h_negative : Derives Γ ((ForcingCodeStep.negative R H w z f j a A B C h n Q).imp (ForcingCodeStep.negative R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .hyp (Or.inl rfl)
  have h_b0 : Derives Γ ((ForcingCodeStep.binary 0 R w z f j a A B C h n Q).imp (ForcingCodeStep.negative R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 0 1 4 (by decide) R w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b1 : Derives Γ ((ForcingCodeStep.binary 1 R w z f j a A B C h n Q).imp (ForcingCodeStep.negative R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 1 1 4 (by decide) R w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b2 : Derives Γ ((ForcingCodeStep.binary 2 R w z f j a A B C h n Q).imp (ForcingCodeStep.negative R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 2 1 4 (by decide) R w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b3 : Derives Γ ((ForcingCodeStep.binary 3 R w z f j a A B C h n Q).imp (ForcingCodeStep.negative R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 3 1 4 (by decide) R w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_universal : Derives Γ ((ForcingCodeStep.universal R H w z f j a A B C h n Q).imp (ForcingCodeStep.negative R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (universal_reject (ZFContext.add hZ _) 1 4 (by decide) R H w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_existential : Derives Γ ((ForcingCodeStep.existential R H w z f j a A B C h n Q).imp (ForcingCodeStep.negative R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (existential_reject (ZFContext.add hZ _) 1 4 (by decide) R H w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  exact .impE (FormulaCodeCaseLogic.disj_imp h_atomic (FormulaCodeCaseLogic.disj_imp h_negative (FormulaCodeCaseLogic.disj_imp h_b0 (FormulaCodeCaseLogic.disj_imp h_b1 (FormulaCodeCaseLogic.disj_imp h_b2 (FormulaCodeCaseLogic.disj_imp h_b3 (FormulaCodeCaseLogic.disj_imp h_universal h_existential))))))) hs

private theorem select_b0 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x y : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 5 w (SyntaxAtomSyntax.two x y) n))
    (hs : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n Q)) : Derives Γ (ForcingCodeStep.binary 0 R w z f j a A B C h n Q) := by
  have h_atomic : Derives Γ (((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q)).imp (ForcingCodeStep.binary 0 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (FormulaCodeCaseLogic.atomic_conflict (ZFContext.add hZ _) 2 5 (by decide) (by decide) (by decide) (by decide) w a z n (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.conjL (.hyp (Or.inl rfl))))
  have h_negative : Derives Γ ((ForcingCodeStep.negative R H w z f j a A B C h n Q).imp (ForcingCodeStep.binary 0 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (negative_reject (ZFContext.add hZ _) 2 5 (by decide) R H w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b0 : Derives Γ ((ForcingCodeStep.binary 0 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 0 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .hyp (Or.inl rfl)
  have h_b1 : Derives Γ ((ForcingCodeStep.binary 1 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 0 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 1 2 5 (by decide) R w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b2 : Derives Γ ((ForcingCodeStep.binary 2 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 0 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 2 2 5 (by decide) R w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b3 : Derives Γ ((ForcingCodeStep.binary 3 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 0 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 3 2 5 (by decide) R w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_universal : Derives Γ ((ForcingCodeStep.universal R H w z f j a A B C h n Q).imp (ForcingCodeStep.binary 0 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (universal_reject (ZFContext.add hZ _) 2 5 (by decide) R H w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_existential : Derives Γ ((ForcingCodeStep.existential R H w z f j a A B C h n Q).imp (ForcingCodeStep.binary 0 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (existential_reject (ZFContext.add hZ _) 2 5 (by decide) R H w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  exact .impE (FormulaCodeCaseLogic.disj_imp h_atomic (FormulaCodeCaseLogic.disj_imp h_negative (FormulaCodeCaseLogic.disj_imp h_b0 (FormulaCodeCaseLogic.disj_imp h_b1 (FormulaCodeCaseLogic.disj_imp h_b2 (FormulaCodeCaseLogic.disj_imp h_b3 (FormulaCodeCaseLogic.disj_imp h_universal h_existential))))))) hs

private theorem select_b1 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x y : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 6 w (SyntaxAtomSyntax.two x y) n))
    (hs : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n Q)) : Derives Γ (ForcingCodeStep.binary 1 R w z f j a A B C h n Q) := by
  have h_atomic : Derives Γ (((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q)).imp (ForcingCodeStep.binary 1 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (FormulaCodeCaseLogic.atomic_conflict (ZFContext.add hZ _) 2 6 (by decide) (by decide) (by decide) (by decide) w a z n (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.conjL (.hyp (Or.inl rfl))))
  have h_negative : Derives Γ ((ForcingCodeStep.negative R H w z f j a A B C h n Q).imp (ForcingCodeStep.binary 1 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (negative_reject (ZFContext.add hZ _) 2 6 (by decide) R H w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b0 : Derives Γ ((ForcingCodeStep.binary 0 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 1 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 0 2 6 (by decide) R w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b1 : Derives Γ ((ForcingCodeStep.binary 1 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 1 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .hyp (Or.inl rfl)
  have h_b2 : Derives Γ ((ForcingCodeStep.binary 2 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 1 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 2 2 6 (by decide) R w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b3 : Derives Γ ((ForcingCodeStep.binary 3 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 1 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 3 2 6 (by decide) R w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_universal : Derives Γ ((ForcingCodeStep.universal R H w z f j a A B C h n Q).imp (ForcingCodeStep.binary 1 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (universal_reject (ZFContext.add hZ _) 2 6 (by decide) R H w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_existential : Derives Γ ((ForcingCodeStep.existential R H w z f j a A B C h n Q).imp (ForcingCodeStep.binary 1 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (existential_reject (ZFContext.add hZ _) 2 6 (by decide) R H w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  exact .impE (FormulaCodeCaseLogic.disj_imp h_atomic (FormulaCodeCaseLogic.disj_imp h_negative (FormulaCodeCaseLogic.disj_imp h_b0 (FormulaCodeCaseLogic.disj_imp h_b1 (FormulaCodeCaseLogic.disj_imp h_b2 (FormulaCodeCaseLogic.disj_imp h_b3 (FormulaCodeCaseLogic.disj_imp h_universal h_existential))))))) hs

private theorem select_b2 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x y : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two x y) n))
    (hs : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n Q)) : Derives Γ (ForcingCodeStep.binary 2 R w z f j a A B C h n Q) := by
  have h_atomic : Derives Γ (((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q)).imp (ForcingCodeStep.binary 2 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (FormulaCodeCaseLogic.atomic_conflict (ZFContext.add hZ _) 2 7 (by decide) (by decide) (by decide) (by decide) w a z n (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.conjL (.hyp (Or.inl rfl))))
  have h_negative : Derives Γ ((ForcingCodeStep.negative R H w z f j a A B C h n Q).imp (ForcingCodeStep.binary 2 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (negative_reject (ZFContext.add hZ _) 2 7 (by decide) R H w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b0 : Derives Γ ((ForcingCodeStep.binary 0 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 2 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 0 2 7 (by decide) R w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b1 : Derives Γ ((ForcingCodeStep.binary 1 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 2 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 1 2 7 (by decide) R w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b2 : Derives Γ ((ForcingCodeStep.binary 2 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 2 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .hyp (Or.inl rfl)
  have h_b3 : Derives Γ ((ForcingCodeStep.binary 3 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 2 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 3 2 7 (by decide) R w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_universal : Derives Γ ((ForcingCodeStep.universal R H w z f j a A B C h n Q).imp (ForcingCodeStep.binary 2 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (universal_reject (ZFContext.add hZ _) 2 7 (by decide) R H w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_existential : Derives Γ ((ForcingCodeStep.existential R H w z f j a A B C h n Q).imp (ForcingCodeStep.binary 2 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (existential_reject (ZFContext.add hZ _) 2 7 (by decide) R H w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  exact .impE (FormulaCodeCaseLogic.disj_imp h_atomic (FormulaCodeCaseLogic.disj_imp h_negative (FormulaCodeCaseLogic.disj_imp h_b0 (FormulaCodeCaseLogic.disj_imp h_b1 (FormulaCodeCaseLogic.disj_imp h_b2 (FormulaCodeCaseLogic.disj_imp h_b3 (FormulaCodeCaseLogic.disj_imp h_universal h_existential))))))) hs

private theorem select_b3 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x y : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 8 w (SyntaxAtomSyntax.two x y) n))
    (hs : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n Q)) : Derives Γ (ForcingCodeStep.binary 3 R w z f j a A B C h n Q) := by
  have h_atomic : Derives Γ (((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q)).imp (ForcingCodeStep.binary 3 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (FormulaCodeCaseLogic.atomic_conflict (ZFContext.add hZ _) 2 8 (by decide) (by decide) (by decide) (by decide) w a z n (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.conjL (.hyp (Or.inl rfl))))
  have h_negative : Derives Γ ((ForcingCodeStep.negative R H w z f j a A B C h n Q).imp (ForcingCodeStep.binary 3 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (negative_reject (ZFContext.add hZ _) 2 8 (by decide) R H w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b0 : Derives Γ ((ForcingCodeStep.binary 0 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 3 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 0 2 8 (by decide) R w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b1 : Derives Γ ((ForcingCodeStep.binary 1 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 3 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 1 2 8 (by decide) R w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b2 : Derives Γ ((ForcingCodeStep.binary 2 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 3 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 2 2 8 (by decide) R w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b3 : Derives Γ ((ForcingCodeStep.binary 3 R w z f j a A B C h n Q).imp (ForcingCodeStep.binary 3 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .hyp (Or.inl rfl)
  have h_universal : Derives Γ ((ForcingCodeStep.universal R H w z f j a A B C h n Q).imp (ForcingCodeStep.binary 3 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (universal_reject (ZFContext.add hZ _) 2 8 (by decide) R H w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_existential : Derives Γ ((ForcingCodeStep.existential R H w z f j a A B C h n Q).imp (ForcingCodeStep.binary 3 R w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (existential_reject (ZFContext.add hZ _) 2 8 (by decide) R H w z f j a A B C h n Q (SyntaxAtomSyntax.two x y) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  exact .impE (FormulaCodeCaseLogic.disj_imp h_atomic (FormulaCodeCaseLogic.disj_imp h_negative (FormulaCodeCaseLogic.disj_imp h_b0 (FormulaCodeCaseLogic.disj_imp h_b1 (FormulaCodeCaseLogic.disj_imp h_b2 (FormulaCodeCaseLogic.disj_imp h_b3 (FormulaCodeCaseLogic.disj_imp h_universal h_existential))))))) hs

private theorem select_universal {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 1 9 w (fun _ => x) n))
    (hs : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n Q)) : Derives Γ (ForcingCodeStep.universal R H w z f j a A B C h n Q) := by
  have h_atomic : Derives Γ (((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q)).imp (ForcingCodeStep.universal R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (FormulaCodeCaseLogic.atomic_conflict (ZFContext.add hZ _) 1 9 (by decide) (by decide) (by decide) (by decide) w a z n (fun _ => x) (add hw _) (add hc _) (.conjL (.hyp (Or.inl rfl))))
  have h_negative : Derives Γ ((ForcingCodeStep.negative R H w z f j a A B C h n Q).imp (ForcingCodeStep.universal R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (negative_reject (ZFContext.add hZ _) 1 9 (by decide) R H w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b0 : Derives Γ ((ForcingCodeStep.binary 0 R w z f j a A B C h n Q).imp (ForcingCodeStep.universal R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 0 1 9 (by decide) R w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b1 : Derives Γ ((ForcingCodeStep.binary 1 R w z f j a A B C h n Q).imp (ForcingCodeStep.universal R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 1 1 9 (by decide) R w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b2 : Derives Γ ((ForcingCodeStep.binary 2 R w z f j a A B C h n Q).imp (ForcingCodeStep.universal R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 2 1 9 (by decide) R w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b3 : Derives Γ ((ForcingCodeStep.binary 3 R w z f j a A B C h n Q).imp (ForcingCodeStep.universal R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 3 1 9 (by decide) R w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_universal : Derives Γ ((ForcingCodeStep.universal R H w z f j a A B C h n Q).imp (ForcingCodeStep.universal R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .hyp (Or.inl rfl)
  have h_existential : Derives Γ ((ForcingCodeStep.existential R H w z f j a A B C h n Q).imp (ForcingCodeStep.universal R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (existential_reject (ZFContext.add hZ _) 1 9 (by decide) R H w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  exact .impE (FormulaCodeCaseLogic.disj_imp h_atomic (FormulaCodeCaseLogic.disj_imp h_negative (FormulaCodeCaseLogic.disj_imp h_b0 (FormulaCodeCaseLogic.disj_imp h_b1 (FormulaCodeCaseLogic.disj_imp h_b2 (FormulaCodeCaseLogic.disj_imp h_b3 (FormulaCodeCaseLogic.disj_imp h_universal h_existential))))))) hs

private theorem select_existential {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 1 10 w (fun _ => x) n))
    (hs : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n Q)) : Derives Γ (ForcingCodeStep.existential R H w z f j a A B C h n Q) := by
  have h_atomic : Derives Γ (((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q)).imp (ForcingCodeStep.existential R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (FormulaCodeCaseLogic.atomic_conflict (ZFContext.add hZ _) 1 10 (by decide) (by decide) (by decide) (by decide) w a z n (fun _ => x) (add hw _) (add hc _) (.conjL (.hyp (Or.inl rfl))))
  have h_negative : Derives Γ ((ForcingCodeStep.negative R H w z f j a A B C h n Q).imp (ForcingCodeStep.existential R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (negative_reject (ZFContext.add hZ _) 1 10 (by decide) R H w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b0 : Derives Γ ((ForcingCodeStep.binary 0 R w z f j a A B C h n Q).imp (ForcingCodeStep.existential R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 0 1 10 (by decide) R w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b1 : Derives Γ ((ForcingCodeStep.binary 1 R w z f j a A B C h n Q).imp (ForcingCodeStep.existential R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 1 1 10 (by decide) R w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b2 : Derives Γ ((ForcingCodeStep.binary 2 R w z f j a A B C h n Q).imp (ForcingCodeStep.existential R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 2 1 10 (by decide) R w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_b3 : Derives Γ ((ForcingCodeStep.binary 3 R w z f j a A B C h n Q).imp (ForcingCodeStep.existential R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (binary_reject (ZFContext.add hZ _) 3 1 10 (by decide) R w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_universal : Derives Γ ((ForcingCodeStep.universal R H w z f j a A B C h n Q).imp (ForcingCodeStep.existential R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .botE (universal_reject (ZFContext.add hZ _) 1 10 (by decide) R H w z f j a A B C h n Q (fun _ => x) (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  have h_existential : Derives Γ ((ForcingCodeStep.existential R H w z f j a A B C h n Q).imp (ForcingCodeStep.existential R H w z f j a A B C h n Q)) := by
    apply Derives.impI
    exact .hyp (Or.inl rfl)
  exact .impE (FormulaCodeCaseLogic.disj_imp h_atomic (FormulaCodeCaseLogic.disj_imp h_negative (FormulaCodeCaseLogic.disj_imp h_b0 (FormulaCodeCaseLogic.disj_imp h_b1 (FormulaCodeCaseLogic.disj_imp h_b2 (FormulaCodeCaseLogic.disj_imp h_b3 (FormulaCodeCaseLogic.disj_imp h_universal h_existential))))))) hs

private theorem atomic_vs_cases {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V : Fin m)
    (hw : Derives Γ (omega w)) (_hf : Derives Γ (functional w f h n))
    (hq : Derives Γ ((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q)))
    (hv : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n V)) : Derives Γ (.equal Q V) := by
  exact ForcingAtomCode.unique hZ R w a z n Q V hw (.conjR hq) (.conjR (select_atomic hZ R H w z f j a A B C h n V hw (.conjL hq) hv))

private theorem negative_vs_cases {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (hq : Derives Γ (ForcingCodeStep.negative R H w z f j a A B C h n Q))
    (hv : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n V)) : Derives Γ (.equal Q V) := by
  let T := negativeBody R H w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T)
  have hf1 : Derives Δ (functional (old 2 w) (old 2 f) (old 2 h) (old 2 n)) := of_eq (functional_rename w f h n (old 2)) (HornBinderRules.under_body 2 hf T)
  have hv1 : Derives Δ (ForcingCodeStep.cases R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 V)) := of_eq (ForcingCodeStep.cases_rename R H w z f j a A B C h n V (old 2)) (HornBinderRules.under_body 2 hv T)
  have hs := select_negative (HornBinderRules.zf_body 2 hZ T) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 V) (slot 2 0) hw1 (.conjL (.conjL hT)) hv1
  exact negative_at_data_unique (HornBinderRules.zf_body 2 hZ T) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 Q) (old 2 V) (slot 2 0) (slot 2 1) hw1 hf1 hT hs

private theorem b0_vs_cases {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (hq : Derives Γ (ForcingCodeStep.binary 0 R w z f j a A B C h n Q))
    (hv : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n V)) : Derives Γ (.equal Q V) := by
  let T := binaryBody 0 R w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw T)
  have hf1 : Derives Δ (functional (old 4 w) (old 4 f) (old 4 h) (old 4 n)) := of_eq (functional_rename w f h n (old 4)) (HornBinderRules.under_body 4 hf T)
  have hv1 : Derives Δ (ForcingCodeStep.cases R H (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 h) (old 4 n) (old 4 V)) := of_eq (ForcingCodeStep.cases_rename R H w z f j a A B C h n V (old 4)) (HornBinderRules.under_body 4 hv T)
  have hs := select_b0 (HornBinderRules.zf_body 4 hZ T) R H (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 h) (old 4 n) (old 4 V) (slot 4 0) (slot 4 1) hw1 (.conjL (.conjL hT)) hv1
  exact binary_at_data_unique (HornBinderRules.zf_body 4 hZ T) 0 R (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 h) (old 4 n) (old 4 Q) (old 4 V) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw1 hf1 hT hs

private theorem b1_vs_cases {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (hq : Derives Γ (ForcingCodeStep.binary 1 R w z f j a A B C h n Q))
    (hv : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n V)) : Derives Γ (.equal Q V) := by
  let T := binaryBody 1 R w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw T)
  have hf1 : Derives Δ (functional (old 4 w) (old 4 f) (old 4 h) (old 4 n)) := of_eq (functional_rename w f h n (old 4)) (HornBinderRules.under_body 4 hf T)
  have hv1 : Derives Δ (ForcingCodeStep.cases R H (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 h) (old 4 n) (old 4 V)) := of_eq (ForcingCodeStep.cases_rename R H w z f j a A B C h n V (old 4)) (HornBinderRules.under_body 4 hv T)
  have hs := select_b1 (HornBinderRules.zf_body 4 hZ T) R H (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 h) (old 4 n) (old 4 V) (slot 4 0) (slot 4 1) hw1 (.conjL (.conjL hT)) hv1
  exact binary_at_data_unique (HornBinderRules.zf_body 4 hZ T) 1 R (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 h) (old 4 n) (old 4 Q) (old 4 V) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw1 hf1 hT hs

private theorem b2_vs_cases {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (hq : Derives Γ (ForcingCodeStep.binary 2 R w z f j a A B C h n Q))
    (hv : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n V)) : Derives Γ (.equal Q V) := by
  let T := binaryBody 2 R w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw T)
  have hf1 : Derives Δ (functional (old 4 w) (old 4 f) (old 4 h) (old 4 n)) := of_eq (functional_rename w f h n (old 4)) (HornBinderRules.under_body 4 hf T)
  have hv1 : Derives Δ (ForcingCodeStep.cases R H (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 h) (old 4 n) (old 4 V)) := of_eq (ForcingCodeStep.cases_rename R H w z f j a A B C h n V (old 4)) (HornBinderRules.under_body 4 hv T)
  have hs := select_b2 (HornBinderRules.zf_body 4 hZ T) R H (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 h) (old 4 n) (old 4 V) (slot 4 0) (slot 4 1) hw1 (.conjL (.conjL hT)) hv1
  exact binary_at_data_unique (HornBinderRules.zf_body 4 hZ T) 2 R (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 h) (old 4 n) (old 4 Q) (old 4 V) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw1 hf1 hT hs

private theorem b3_vs_cases {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (hq : Derives Γ (ForcingCodeStep.binary 3 R w z f j a A B C h n Q))
    (hv : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n V)) : Derives Γ (.equal Q V) := by
  let T := binaryBody 3 R w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw T)
  have hf1 : Derives Δ (functional (old 4 w) (old 4 f) (old 4 h) (old 4 n)) := of_eq (functional_rename w f h n (old 4)) (HornBinderRules.under_body 4 hf T)
  have hv1 : Derives Δ (ForcingCodeStep.cases R H (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 h) (old 4 n) (old 4 V)) := of_eq (ForcingCodeStep.cases_rename R H w z f j a A B C h n V (old 4)) (HornBinderRules.under_body 4 hv T)
  have hs := select_b3 (HornBinderRules.zf_body 4 hZ T) R H (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 h) (old 4 n) (old 4 V) (slot 4 0) (slot 4 1) hw1 (.conjL (.conjL hT)) hv1
  exact binary_at_data_unique (HornBinderRules.zf_body 4 hZ T) 3 R (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 h) (old 4 n) (old 4 Q) (old 4 V) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw1 hf1 hT hs

private theorem universal_vs_cases {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (hq : Derives Γ (ForcingCodeStep.universal R H w z f j a A B C h n Q))
    (hv : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n V)) : Derives Γ (.equal Q V) := by
  let T := universalBody R H w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T)
  have hf1 : Derives Δ (functional (old 2 w) (old 2 f) (old 2 h) (old 2 n)) := of_eq (functional_rename w f h n (old 2)) (HornBinderRules.under_body 2 hf T)
  have hv1 : Derives Δ (ForcingCodeStep.cases R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 V)) := of_eq (ForcingCodeStep.cases_rename R H w z f j a A B C h n V (old 2)) (HornBinderRules.under_body 2 hv T)
  have hs := select_universal (HornBinderRules.zf_body 2 hZ T) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 V) (slot 2 0) hw1 (.conjL (.conjL hT)) hv1
  exact universal_at_data_unique (HornBinderRules.zf_body 2 hZ T) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 Q) (old 2 V) (slot 2 0) (slot 2 1) hw1 hf1 hT hs

private theorem existential_vs_cases {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (hq : Derives Γ (ForcingCodeStep.existential R H w z f j a A B C h n Q))
    (hv : Derives Γ (ForcingCodeStep.cases R H w z f j a A B C h n V)) : Derives Γ (.equal Q V) := by
  let T := existentialBody R H w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T)
  have hf1 : Derives Δ (functional (old 2 w) (old 2 f) (old 2 h) (old 2 n)) := of_eq (functional_rename w f h n (old 2)) (HornBinderRules.under_body 2 hf T)
  have hv1 : Derives Δ (ForcingCodeStep.cases R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 V)) := of_eq (ForcingCodeStep.cases_rename R H w z f j a A B C h n V (old 2)) (HornBinderRules.under_body 2 hv T)
  have hs := select_existential (HornBinderRules.zf_body 2 hZ T) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 V) (slot 2 0) hw1 (.conjL (.conjL hT)) hv1
  exact existential_at_data_unique (HornBinderRules.zf_body 2 hZ T) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 Q) (old 2 V) (slot 2 0) (slot 2 1) hw1 hf1 hT hs

theorem unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functional w f h n))
    (hq : Derives Γ (ForcingCodeStep.step R H w z f j a A B C h n Q))
    (hv : Derives Γ (ForcingCodeStep.step R H w z f j a A B C h n V)) : Derives Γ (.equal Q V) := by
  have h_atomic : Derives Γ (((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q)).imp (.equal Q V)) := by
    apply Derives.impI
    exact atomic_vs_cases (ZFContext.add hZ _) R H w z f j a A B C h n Q V (add hw _) (add hf _) (.hyp (Or.inl rfl)) (add (.conjR hv) _)
  have h_negative : Derives Γ ((ForcingCodeStep.negative R H w z f j a A B C h n Q).imp (.equal Q V)) := by
    apply Derives.impI
    exact negative_vs_cases (ZFContext.add hZ _) R H w z f j a A B C h n Q V (add hw _) (add hf _) (.hyp (Or.inl rfl)) (add (.conjR hv) _)
  have h_b0 : Derives Γ ((ForcingCodeStep.binary 0 R w z f j a A B C h n Q).imp (.equal Q V)) := by
    apply Derives.impI
    exact b0_vs_cases (ZFContext.add hZ _) R H w z f j a A B C h n Q V (add hw _) (add hf _) (.hyp (Or.inl rfl)) (add (.conjR hv) _)
  have h_b1 : Derives Γ ((ForcingCodeStep.binary 1 R w z f j a A B C h n Q).imp (.equal Q V)) := by
    apply Derives.impI
    exact b1_vs_cases (ZFContext.add hZ _) R H w z f j a A B C h n Q V (add hw _) (add hf _) (.hyp (Or.inl rfl)) (add (.conjR hv) _)
  have h_b2 : Derives Γ ((ForcingCodeStep.binary 2 R w z f j a A B C h n Q).imp (.equal Q V)) := by
    apply Derives.impI
    exact b2_vs_cases (ZFContext.add hZ _) R H w z f j a A B C h n Q V (add hw _) (add hf _) (.hyp (Or.inl rfl)) (add (.conjR hv) _)
  have h_b3 : Derives Γ ((ForcingCodeStep.binary 3 R w z f j a A B C h n Q).imp (.equal Q V)) := by
    apply Derives.impI
    exact b3_vs_cases (ZFContext.add hZ _) R H w z f j a A B C h n Q V (add hw _) (add hf _) (.hyp (Or.inl rfl)) (add (.conjR hv) _)
  have h_universal : Derives Γ ((ForcingCodeStep.universal R H w z f j a A B C h n Q).imp (.equal Q V)) := by
    apply Derives.impI
    exact universal_vs_cases (ZFContext.add hZ _) R H w z f j a A B C h n Q V (add hw _) (add hf _) (.hyp (Or.inl rfl)) (add (.conjR hv) _)
  have h_existential : Derives Γ ((ForcingCodeStep.existential R H w z f j a A B C h n Q).imp (.equal Q V)) := by
    apply Derives.impI
    exact existential_vs_cases (ZFContext.add hZ _) R H w z f j a A B C h n Q V (add hw _) (add hf _) (.hyp (Or.inl rfl)) (add (.conjR hv) _)
  exact .impE (FormulaCodeCaseLogic.disj_imp h_atomic (FormulaCodeCaseLogic.disj_imp h_negative (FormulaCodeCaseLogic.disj_imp h_b0 (FormulaCodeCaseLogic.disj_imp h_b1 (FormulaCodeCaseLogic.disj_imp h_b2 (FormulaCodeCaseLogic.disj_imp h_b3 (FormulaCodeCaseLogic.disj_imp h_universal h_existential))))))) (.conjR hq)

def sentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V : Fin m) : Source.Sentence :=
  ((omega w).imp ((functional w f h n).imp ((ForcingCodeStep.step R H w z f j a A B C h n Q).imp
    ((ForcingCodeStep.step R H w z f j a A B C h n V).imp (.equal Q V))))).close

theorem kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q V : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R H w z f j a A B C h n Q V)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact unique (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) R H w z f j a A B C h n Q V
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
end PPAC.Migration.ForcingCodeStepUnique
