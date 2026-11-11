import PPAC.Migration.ForcingRawModalBody
import PPAC.Migration.NativeProofQuotation
import PPAC.Migration.ForcingSourceMono

/-! Monotonicity of the actual outputs for the original logical
normalizations. The already established negative and conjunction rules
consume the constructor records of the very same compiled outputs. -/
namespace PPAC.Migration.ForcingSourceLogicalMono
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open ForcingConjunctionMono (transfer transfer_rename)
open ForcingSourceMono (atSource atSource_rename apply_atSource)
open NativeProofQuotation (eliminate_objects)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def negativeBody {k m} (Reln : Formula (k+2)) (w a A f j N Q : Fin m) : Formula m :=
  (formulaCode w N a f).conj (ForcingNegCode.compiled Reln w a A f j N Q)

private theorem negativeBody_rename {k m l} (Reln : Formula (k+2)) (w a A f j N Q : Fin m)
    (r : Fin m → Fin l) :
    (negativeBody Reln w a A f j N Q).rename r =
      negativeBody Reln (r w) (r a) (r A) (r f) (r j) (r N) (r Q) := by
  simp only [negativeBody, Formula.rename, formulaCode_rename, ForcingNegCode.compiled_rename]

def negativeInput {k m} (Reln : Formula (k+2)) (w a A f j Q : Fin m) : Formula m :=
  .ex (negativeBody Reln w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc (Fin.last m) Q.castSucc)

theorem negativeInput_rename {k m l} (Reln : Formula (k+2)) (w a A f j Q : Fin m)
    (r : Fin m → Fin l) :
    (negativeInput Reln w a A f j Q).rename r =
      negativeInput Reln (r w) (r a) (r A) (r f) (r j) (r Q) := by
  simp only [negativeInput, Formula.rename, negativeBody_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem intro_negativeInput {k m} {Γ : Context m} (Reln : Formula (k+2)) (w a A f j N Q : Fin m)
    (hn : Derives Γ (formulaCode w N a f)) (hq : Derives Γ (ForcingNegCode.compiled Reln w a A f j N Q)) :
    Derives Γ (negativeInput Reln w a A f j Q) := by
  apply Derives.exI N
  exact of_eq (by simp only [Formula.instantiate, negativeBody_rename, Fin.lastCases_last,
    Fin.lastCases_castSucc, id_eq] <;> rfl) (.conjI hn hq : Derives Γ (negativeBody Reln w a A f j N Q))

private abbrev conjunctionCode {m} (w a f X Y Q : Fin m) : Formula m :=
  FormulaCodeConstructSyntax.typedAt 2 5 w (SyntaxAtomSyntax.two X Y) Q a f

theorem disjunction_input {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w a A f j X Y Q : Fin m)
    (h : Derives Γ (ForcingLogicalCode.binary 1 Reln w a A f j X Y Q)) :
    Derives Γ (negativeInput Reln w a A f j Q) := by
  apply eliminate_objects hZ 3 (fun r v =>
    (ForcingNegCode.compiled Reln (r w) (r a) (r A) (r f) (r j) (r X) (v 0)).conj
      ((ForcingNegCode.compiled Reln (r w) (r a) (r A) (r f) (r j) (r Y) (v 1)).conj
        ((conjunctionCode (r w) (r a) (r f) (v 0) (v 1) (v 2)).conj
          (ForcingNegCode.compiled Reln (r w) (r a) (r A) (r f) (r j) (v 2) (r Q))))) h
    (negativeInput Reln w a A f j Q)
  intro l Δ r v _ _ hd
  exact of_eq (negativeInput_rename Reln w a A f j Q r).symm
    (intro_negativeInput Reln (r w) (r a) (r A) (r f) (r j) (v 2) (r Q)
      (.conjR (.conjL (.conjR (.conjR hd)))) (.conjR (.conjR (.conjR hd))))

theorem implication_input {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w a A f j X Y Q : Fin m)
    (h : Derives Γ (ForcingLogicalCode.binary 2 Reln w a A f j X Y Q)) :
    Derives Γ (negativeInput Reln w a A f j Q) := by
  apply eliminate_objects hZ 2 (fun r v =>
    (ForcingNegCode.compiled Reln (r w) (r a) (r A) (r f) (r j) (r Y) (v 0)).conj
      ((conjunctionCode (r w) (r a) (r f) (r X) (v 0) (v 1)).conj
        (ForcingNegCode.compiled Reln (r w) (r a) (r A) (r f) (r j) (v 1) (r Q)))) h
    (negativeInput Reln w a A f j Q)
  intro l Δ r v _ _ hd
  exact of_eq (negativeInput_rename Reln w a A f j Q r).symm
    (intro_negativeInput Reln (r w) (r a) (r A) (r f) (r j) (v 1) (r Q)
      (.conjR (.conjL (.conjR hd))) (.conjR (.conjR hd)))

theorem universal_input {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1)) (w a A B C f j X Q : Fin m)
    (h : Derives Γ (ForcingLogicalCode.universal Reln Dom w a A B C f j X Q)) :
    Derives Γ (negativeInput Reln w a A f j Q) := by
  apply eliminate_objects hZ 2 (fun r v =>
    (ForcingNegCode.compiled Reln (r w) (r A) (r B) (r f) (r j) (r X) (v 0)).conj
      ((ForcingExistCode.compiled Reln Dom (r w) (r a) (r A) (r B) (r C) (r f) (r j) (v 0) (v 1)).conj
        (ForcingNegCode.compiled Reln (r w) (r a) (r A) (r f) (r j) (v 1) (r Q)))) h
    (negativeInput Reln w a A f j Q)
  intro l Δ r v _ _ hd
  exact of_eq (negativeInput_rename Reln w a A f j Q r).symm
    (intro_negativeInput Reln (r w) (r a) (r A) (r f) (r j) (v 1) (r Q)
      (ForcingExistCode.compiled_type Reln Dom (r w) (r a) (r A) (r B) (r C)
        (r f) (r j) (v 0) (v 1) (.conjL (.conjR hd))) (.conjR (.conjR hd)))

def negativeLaw {k m} (test : Formula 1) (Reln : Formula (k+2)) (w z a A f j b G : Fin m)
    (R S : Fin 2 → Fin m) : Formula m := .all
  ((negativeInput Reln w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc (Fin.last m)).imp
    (transfer test w.castSucc z.castSucc a.castSucc f.castSucc b.castSucc G.castSucc
      (fun i => (R i).castSucc) (fun i => (S i).castSucc) (Fin.last m)))

theorem negativeLaw_rename {k m l} (test : Formula 1) (Reln : Formula (k+2)) (w z a A f j b G : Fin m)
    (R S : Fin 2 → Fin m) (r : Fin m → Fin l) :
    (negativeLaw test Reln w z a A f j b G R S).rename r =
      negativeLaw test Reln (r w) (r z) (r a) (r A) (r f) (r j) (r b) (r G)
        (fun i => r (R i)) (fun i => r (S i)) := by
  simp only [negativeLaw, Formula.rename, negativeInput_rename, transfer_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem apply_negativeLaw {k m} {Γ : Context m} (test : Formula 1) (Reln : Formula (k+2))
    (w z a A f j b G Q : Fin m) (R S : Fin 2 → Fin m)
    (hl : Derives Γ (negativeLaw test Reln w z a A f j b G R S))
    (h : Derives Γ (negativeInput Reln w a A f j Q)) :
    Derives Γ (transfer test w z a f b G R S Q) := by
  have h' : Derives Γ ((negativeInput Reln w a A f j Q).imp (transfer test w z a f b G R S Q)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, negativeInput_rename, transfer_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE Q hl)
  exact .impE h' h

/-- The negative law is an object consequence of the same global row and
scope successor used by the original negative source case. -/
theorem negativeLaw_of_runtime {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Formula (k+2))
    (w z a f j b B R S T S0 S1 A1 A2 A3 K Extra A : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m)
    (hr : Derives Γ (ForcingRawModalBody.globalModalInput test Reln w z a f j b B R S T S0 S1 A1 A2 A3 K Extra
      raw v C Refl Pre U0 P rows layout))
    (hs : Derives Γ (successor A a)) :
    Derives Γ (negativeLaw test Reln w z a A f j b (layout 3) (fun _ => T) (SyntaxAtomSyntax.two S0 S1)) := by
  apply Derives.allI
  apply Derives.impI
  let r : Fin m → Fin (m+1) := Fin.castSucc
  let q := Fin.last m
  let E := negativeInput Reln (r w) (r a) (r A) (r f) (r j) q
  let Δ := Context.add E (Context.image Formula.raise Γ)
  let out := transfer test (r w) (r z) (r a) (r f) (r b) (r (layout 3))
    (fun _ => r T) (fun i => r (SyntaxAtomSyntax.two S0 S1 i)) q
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  apply eliminate_objects (ZFContext.under hZ E) 1 (fun s xs =>
    negativeBody Reln (s (r w)) (s (r a)) (s (r A)) (s (r f)) (s (r j)) (xs 0) (s q)) hE out
  intro l Ξ s xs hZ1 lift hNeg
  let ρ := fun i => s (r i)
  have carry {φ : Formula m} (h : Derives Γ φ) : Derives Ξ (φ.rename ρ) :=
    of_eq (rename_comp φ r s) (lift (under h E))
  have hRuntime := of_eq (ForcingRawModalBody.globalModalInput_rename test Reln w z a f j b B R S T S0 S1 A1 A2 A3 K
    Extra raw v C Refl Pre U0 P rows layout ρ) (carry hr)
  have result := ForcingRawModalBody.transfer_negative_global hZ1 test Reln
    (ρ w) (ρ z) (ρ a) (ρ f) (ρ j) (ρ b) (ρ B) (ρ R) (ρ S) (ρ T) (ρ S0) (ρ S1)
    (ρ A1) (ρ A2) (ρ A3) (ρ K) (ρ Extra)
    (fun i => ρ (raw i)) (fun i => ρ (v i)) (fun i => ρ (C i)) (fun i => ρ (Refl i))
    (fun i => ρ (Pre i)) (fun i => ρ (U0 i)) (fun i t => ρ (P i t)) (fun i => ρ (rows i))
    (fun i => ρ (layout i)) (ρ A) (xs 0) (s q)
    (.conjI hRuntime (.conjI (of_eq (successor_rename A a ρ) (carry hs)) hNeg))
  exact of_eq (by simp only [out, transfer_rename, ρ, SyntaxAtomSyntax.two_map]) result

theorem biconditional {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (Reln : Formula (k+2)) (w z a A f j b G X Y Q : Fin m) (R S : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hg : Derives Γ (formulaCode w G z b))
    (hl : Derives Γ (negativeLaw test Reln w z a A f j b G R S))
    (h : Derives Γ (ForcingLogicalCode.binary 3 Reln w a A f j X Y Q)) :
    Derives Γ (transfer test w z a f b G R S Q) := by
  apply eliminate_objects hZ 2 (fun r v =>
    (ForcingLogicalCode.binary 2 Reln (r w) (r a) (r A) (r f) (r j) (r X) (r Y) (v 0)).conj
      ((ForcingLogicalCode.binary 2 Reln (r w) (r a) (r A) (r f) (r j) (r Y) (r X) (v 1)).conj
        (conjunctionCode (r w) (r a) (r f) (v 0) (v 1) (r Q)))) h (transfer test w z a f b G R S Q)
  intro l Δ r v hZ1 lift hd
  have hl1 := of_eq (negativeLaw_rename test Reln w z a A f j b G R S r) (lift hl)
  have left := implication_input hZ1 Reln (r w) (r a) (r A) (r f) (r j) (r X) (r Y) (v 0) (.conjL hd)
  have right := implication_input hZ1 Reln (r w) (r a) (r A) (r f) (r j) (r Y) (r X) (v 1) (.conjL (.conjR hd))
  exact of_eq (transfer_rename test w z a f b G R S Q r).symm
    (ForcingConjunctionMono.conjunction hZ1 test (r w) (r z) (r a) (r f) (r b) (r G)
      (fun i => r (R i)) (fun i => r (S i)) (r Q) (v 0) (v 1)
      (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz))
      (of_eq (formulaCode_rename w G z b r) (lift hg)) (.conjL (.conjR (.conjR hd)))
      (apply_negativeLaw test Reln (r w) (r z) (r a) (r A) (r f) (r j) (r b) (r G) (v 0) _ _ hl1 left)
      (apply_negativeLaw test Reln (r w) (r z) (r a) (r A) (r f) (r j) (r b) (r G) (v 1) _ _ hl1 right))

/-- Consume the actual OR, IMP, or IFF record at the root of the recursive
compiler. Both child codes are read from the same history. -/
theorem binary_step {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (kind : Fin 3) (test : Formula 1) (Reln : Formula (k+2))
    (w z a A B C f j b G h n Q : Fin m) (R S : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hg : Derives Γ (formulaCode w G z b))
    (hl : Derives Γ (negativeLaw test Reln w z a A f j b G R S))
    (hc : Derives Γ (ForcingCodeStep.binary kind.succ Reln w z f j a A B C h n Q)) :
    Derives Γ (transfer test w z a f b G R S Q) := by
  apply eliminate_objects hZ 4 (fun r v => ForcingCodeStep.binaryData kind.succ Reln (r w) (r z) (r f) (r j)
    (r a) (r A) (r B) (r C) (r h) (r n) (r Q) (v 0) (v 1) (v 2) (v 3)) hc
    (transfer test w z a f b G R S Q)
  intro l Δ r v hZ1 lift hd
  apply of_eq (transfer_rename test w z a f b G R S Q r).symm
  have hl1 := of_eq (negativeLaw_rename test Reln w z a A f j b G R S r) (lift hl)
  have hOut : Derives Δ (ForcingLogicalCode.binary kind.succ Reln (r w) (r a) (r A) (r f) (r j) (v 2) (v 3) (r Q)) :=
    .conjR (.conjR (.conjR hd))
  have consume : Derives Δ (negativeInput Reln (r w) (r a) (r A) (r f) (r j) (r Q)) →
      Derives Δ (transfer test (r w) (r z) (r a) (r f) (r b) (r G)
        (fun i => r (R i)) (fun i => r (S i)) (r Q)) :=
    apply_negativeLaw test Reln (r w) (r z) (r a) (r A) (r f) (r j) (r b) (r G) (r Q) _ _ hl1
  revert hOut
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) kind
  · intro hOut
    exact consume (disjunction_input hZ1 Reln (r w) (r a) (r A) (r f) (r j) (v 2) (v 3) (r Q) hOut)
  · intro hOut
    exact consume (implication_input hZ1 Reln (r w) (r a) (r A) (r f) (r j) (v 2) (v 3) (r Q) hOut)
  · intro hOut
    exact biconditional hZ1 test Reln (r w) (r z) (r a) (r A) (r f) (r j) (r b) (r G) (v 2) (v 3) (r Q)
      _ _ (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz))
      (of_eq (formulaCode_rename w G z b r) (lift hg)) hl1 hOut

theorem universal_step {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B C f j b G h n Q : Fin m) (R S : Fin 2 → Fin m)
    (hl : Derives Γ (negativeLaw test Reln w z a A f j b G R S))
    (hc : Derives Γ (ForcingCodeStep.universal Reln Dom w z f j a A B C h n Q)) :
    Derives Γ (transfer test w z a f b G R S Q) := by
  apply eliminate_objects hZ 2 (fun r v =>
    (FormulaCodeRecursiveSyntax.singleFields 9 true (r w) (r a) (r z) (v 0) (r n)).conj
      ((ForcingCodeStep.read (r w) (r h) (v 0) (r A) (r f) (v 1)).conj
        (ForcingLogicalCode.universal Reln Dom (r w) (r a) (r A) (r B) (r C) (r f) (r j) (v 1) (r Q))))
    hc (transfer test w z a f b G R S Q)
  intro l Δ r v hZ1 lift hd
  exact of_eq (transfer_rename test w z a f b G R S Q r).symm
    (apply_negativeLaw test Reln (r w) (r z) (r a) (r A) (r f) (r j) (r b) (r G) (r Q) _ _
      (of_eq (negativeLaw_rename test Reln w z a A f j b G R S r) (lift hl))
      (universal_input hZ1 Reln Dom (r w) (r a) (r A) (r B) (r C) (r f) (r j) (v 1) (r Q) (.conjR (.conjR hd))))

theorem negative_step {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B C f j b G h n Q : Fin m) (R S : Fin 2 → Fin m)
    (hl : Derives Γ (negativeLaw test Reln w z a A f j b G R S))
    (hc : Derives Γ (ForcingCodeStep.negative Reln Dom w z f j a A B C h n Q)) :
    Derives Γ (transfer test w z a f b G R S Q) := by
  apply eliminate_objects hZ 2 (fun r v =>
    (FormulaCodeRecursiveSyntax.singleFields 4 false (r w) (r a) (r z) (v 0) (r n)).conj
      ((ForcingCodeStep.read (r w) (r h) (v 0) (r a) (r f) (v 1)).conj
        (ForcingNegCode.compiled Reln (r w) (r a) (r A) (r f) (r j) (v 1) (r Q))))
    hc (transfer test w z a f b G R S Q)
  intro l Δ r v _ lift hd
  have hx := ForcingCodeStep.read_type (r w) (r h) (v 0) (r a) (r f) (v 1) (.conjL (.conjR hd))
  exact of_eq (transfer_rename test w z a f b G R S Q r).symm
    (apply_negativeLaw test Reln (r w) (r z) (r a) (r A) (r f) (r j) (r b) (r G) (r Q) _ _
      (of_eq (negativeLaw_rename test Reln w z a A f j b G R S r) (lift hl))
      (intro_negativeInput Reln (r w) (r a) (r A) (r f) (r j) (v 1) (r Q) hx (.conjR (.conjR hd))))

def property {k m} (test : Formula 1) (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b G n : Fin m) (R S : Fin 2 → Fin m) : Formula m :=
  (formulaCode w n a z).imp (atSource test Reln Dom w z f j a b G R S n)

theorem property_rename {k m l} (test : Formula 1) (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b G n : Fin m) (R S : Fin 2 → Fin m) (r : Fin m → Fin l) :
    (property test Reln Dom w z a f j b G n R S).rename r =
      property test Reln Dom (r w) (r z) (r a) (r f) (r j) (r b) (r G) (r n)
        (fun i => r (R i)) (fun i => r (S i)) := by
  simp only [property, Formula.rename, formulaCode_rename, atSource_rename]

def below {k m} (test : Formula 1) (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b G n : Fin m) (R S : Fin 2 → Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp
    (property test Reln Dom w.castSucc z.castSucc a.castSucc f.castSucc j.castSucc b.castSucc G.castSucc
      (Fin.last m) (fun i => (R i).castSucc) (fun i => (S i).castSucc))))

theorem below_rename {k m l} (test : Formula 1) (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b G n : Fin m) (R S : Fin 2 → Fin m) (r : Fin m → Fin l) :
    (below test Reln Dom w z a f j b G n R S).rename r =
      below test Reln Dom (r w) (r z) (r a) (r f) (r j) (r b) (r G) (r n)
        (fun i => r (R i)) (fun i => r (S i)) := by
  simp only [below, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem below_at {k m} {Γ : Context m} (test : Formula 1) (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b G n x : Fin m) (R S : Fin 2 → Fin m)
    (h : Derives Γ (below test Reln Dom w z a f j b G n R S))
    (hxn : Derives Γ (.mem x n)) (ht : Derives Γ (formulaCode w x a z)) :
    Derives Γ (atSource test Reln Dom w z f j a b G R S x) := by
  have step : Derives Γ ((Formula.mem x w).imp ((Formula.mem x n).imp
      (property test Reln Dom w z a f j b G x R S))) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last,
      Fin.lastCases_castSucc, id_eq]) (Derives.allE x h)
  exact .impE (.impE (.impE step (.conjL (FormulaCodeProperties.guards w x a z ht))) hxn) ht

/-- For an actual AND record, read both lower source codes and their actual
compiler outputs. Use the object induction hypothesis at those two codes. -/
theorem conjunction_step {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B C f j b G h n Q : Fin m) (R S : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hg : Derives Γ (formulaCode w G z b))
    (hn : Derives Γ (OrdinalSyntax.ordinal n))
    (hh : Derives Γ (ForcingCodeRecursion.graph Reln Dom w z f j h n))
    (hi : Derives Γ (below test Reln Dom w z a f j b G n R S))
    (hc : Derives Γ (ForcingCodeStep.binary 0 Reln w z f j a A B C h n Q)) :
    Derives Γ (transfer test w z a f b G R S Q) := by
  apply eliminate_objects hZ 4 (fun r v => ForcingCodeStep.binaryData 0 Reln (r w) (r z) (r f) (r j)
    (r a) (r A) (r B) (r C) (r h) (r n) (r Q) (v 0) (v 1) (v 2) (v 3)) hc
    (transfer test w z a f b G R S Q)
  intro l Δ r v hZ1 lift hd
  let R' := fun i => r (R i)
  let S' := fun i => r (S i)
  have hx := Derives.conjL (.conjR (.conjL hd))
  have hy := Derives.conjL (.conjR (.conjR (.conjL hd)))
  have hLower := of_eq (below_rename test Reln Dom w z a f j b G n R S r) (lift hi)
  have hn1 := of_eq (OrdinalSyntax.ordinal_rename n r) (lift hn)
  have hGraph := of_eq (ForcingCodeRecursion.graph_rename Reln Dom w z f j h n r) (lift hh)
  have hLeft := ForcingCodeRecursion.read_to_compiled hZ1 Reln Dom (r w) (r z) (r f) (r j) (r h) (r n) (r a)
    (v 0) (v 2) hn1 hx hGraph (.conjL (.conjR hd))
  have hRight := ForcingCodeRecursion.read_to_compiled hZ1 Reln Dom (r w) (r z) (r f) (r j) (r h) (r n) (r a)
    (v 1) (v 3) hn1 hy hGraph (.conjL (.conjR (.conjR hd)))
  have left := below_at test Reln Dom (r w) (r z) (r a) (r f) (r j) (r b) (r G) (r n) (v 0) R' S' hLower hx
    (.conjL (.conjR (.conjR (.conjR (.conjL hd)))))
  have right := below_at test Reln Dom (r w) (r z) (r a) (r f) (r j) (r b) (r G) (r n) (v 1) R' S' hLower hy
    (.conjR (.conjR (.conjR (.conjR (.conjL hd)))))
  exact of_eq (transfer_rename test w z a f b G R S Q r).symm
    (ForcingConjunctionMono.conjunction hZ1 test (r w) (r z) (r a) (r f) (r b) (r G) R' S' (r Q) (v 2) (v 3)
      (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz))
      (of_eq (formulaCode_rename w G z b r) (lift hg)) (.conjL (.conjR (.conjR (.conjR hd))))
      (apply_atSource test Reln Dom (r w) (r z) (r f) (r j) (r a) (r b) (r G) R' S' (v 0) (v 2) left hLeft)
      (apply_atSource test Reln Dom (r w) (r z) (r f) (r j) (r a) (r b) (r G) R' S' (v 1) (v 3) right hRight))

end PPAC.Migration.ForcingSourceLogicalMono
