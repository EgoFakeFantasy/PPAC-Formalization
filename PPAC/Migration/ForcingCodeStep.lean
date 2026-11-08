import PPAC.Migration.ForcingAtomCode
import PPAC.Migration.ForcingLogicalCode
import PPAC.Migration.Internal.SyntaxForestInjective
import PPAC.Migration.Internal.SyntaxForests

/-! Concrete full eleven-constructor forcing-code dispatch. Child calls read
actual internally encoded (scope,output) states from a history graph. This is
the one-step consumer used by the subsequent original ordinal recursion. Its
closure theorem exposes an object-level earlier-history availability premise;
that premise is not a completed recursive interpreter or a Con proof.
Source free scope is the internal empty zero; internal bound scopes/codes are
unrestricted. Open proof nodes still require the existing mixed-substitution
and closure path; they are not silently restricted to closed nodes here. -/
namespace PPAC.Migration.ForcingCodeStep
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
set_option maxRecDepth 16384

def state {m} (w a f Q s : Fin m) : Formula m :=
  (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two a Q) s).conj (formulaCode w Q a f)
theorem state_rename {m l} (w a f Q s : Fin m) (r : Fin m → Fin l) :
    (state w a f Q s).rename r = state (r w) (r a) (r f) (r Q) (r s) := by
  simp only [state, Formula.rename, SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map, formulaCode_rename]

def read {m} (w h x a f Q : Fin m) : Formula m := existsMany 2
  ((GraphSyntax.edge (old 2 h) (old 2 x) (slot 2 0)).conj
    ((Formula.mem (slot 2 1) (slot 2 0)).conj (state (old 2 w) (old 2 a) (old 2 f) (old 2 Q) (slot 2 1))))
theorem read_rename {m l} (w h x a f Q : Fin m) (r : Fin m → Fin l) :
    (read w h x a f Q).rename r = read (r w) (r h) (r x) (r a) (r f) (r Q) := by
  simp only [read, existsMany_rename, Formula.rename, GraphSyntax.edge_rename, state_rename, lift_old, lift_slot]
theorem read_type {m} {Γ : Context m} (w h x a f Q : Fin m) (hr : Derives Γ (read w h x a f Q)) :
    Derives Γ (formulaCode w Q a f) := by
  let T := (GraphSyntax.edge (old 2 h) (old 2 x) (slot 2 0)).conj
    ((Formula.mem (slot 2 1) (slot 2 0)).conj (state (old 2 w) (old 2 a) (old 2 f) (old 2 Q) (slot 2 1)))
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hr
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w Q a f (old 2)).symm (.conjR (.conjR (.conjR hT)))

def existsRead {m} (w h x a f : Fin m) : Formula m := .ex
  (read w.castSucc h.castSucc x.castSucc a.castSucc f.castSucc (Fin.last m))
theorem existsRead_rename {m l} (w h x a f : Fin m) (r : Fin m → Fin l) :
    (existsRead w h x a f).rename r = existsRead (r w) (r h) (r x) (r a) (r f) := by
  simp only [existsRead, Formula.rename, read_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- The exact earlier-history premise to be discharged by recursion induction.
It quantifies all internal source child codes and all internal bound scopes. -/
def available {m} (w z f h n : Fin m) : Formula m := .all (.all
  (((Formula.mem (Fin.last m).castSucc n.castSucc.castSucc).conj
    (formulaCode w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) z.castSucc.castSucc)).imp
    (existsRead w.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) f.castSucc.castSucc)))
theorem available_rename {m l} (w z f h n : Fin m) (r : Fin m → Fin l) :
    (available w z f h n).rename r = available (r w) (r z) (r f) (r h) (r n) := by
  simp only [available, Formula.rename, formulaCode_rename, existsRead_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem available_at {m} {Γ : Context m} (w z f h n x a : Fin m)
    (ha : Derives Γ (available w z f h n)) (hx : Derives Γ (.mem x n)) (hc : Derives Γ (formulaCode w x a z)) :
    Derives Γ (existsRead w h x a f) := by
  have hh : Derives Γ (((Formula.mem x n).conj (formulaCode w x a z)).imp (existsRead w h x a f)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, formulaCode_rename, existsRead_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE a (Derives.allE x ha))
  exact .impE hh (.conjI hx hc)

private structure Inputs {m} (k : Nat) (Γ : Context m) (w z f j a A B C h n : Fin m) : Prop where
  hw : Derives Γ (omega w)
  hz : Derives Γ (empty z)
  hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)
  hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j)
  hA : Derives Γ (successor A a)
  hB : Derives Γ (successor B A)
  hC : Derives Γ (successor C B)
  he : Derives Γ (available w z f h n)
private theorem underInputs {k m} {Γ : Context m} {w z f j a A B C h n : Fin m} (hI : Inputs k Γ w z f j a A B C h n) (T : Formula (m+1)) :
    Inputs k (Context.add T (Context.image Formula.raise Γ)) w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc := by
  exact ⟨of_eq (omega_rename w Fin.castSucc) (under hI.hw T),
    of_eq (empty_rename z Fin.castSucc) (under hI.hz T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f Fin.castSucc) (under hI.hf T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) j Fin.castSucc) (under hI.hj T),
    of_eq (successor_rename A a Fin.castSucc) (under hI.hA T),
    of_eq (successor_rename B A Fin.castSucc) (under hI.hB T),
    of_eq (successor_rename C B Fin.castSucc) (under hI.hC T),
    of_eq (available_rename w z f h n Fin.castSucc) (under hI.he T)⟩

private theorem underInputs2 {k m} {Γ : Context m} {w z f j a A B C h n : Fin m} (hI : Inputs k Γ w z f j a A B C h n) (T : Formula (m+2)) :
    Inputs k (Context.add T (raisedContext 2 Γ)) (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) := by
  exact ⟨of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hI.hw T),
    of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hI.hz T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f (old 2)) (HornBinderRules.under_body 2 hI.hf T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) j (old 2)) (HornBinderRules.under_body 2 hI.hj T),
    of_eq (successor_rename A a (old 2)) (HornBinderRules.under_body 2 hI.hA T),
    of_eq (successor_rename B A (old 2)) (HornBinderRules.under_body 2 hI.hB T),
    of_eq (successor_rename C B (old 2)) (HornBinderRules.under_body 2 hI.hC T),
    of_eq (available_rename w z f h n (old 2)) (HornBinderRules.under_body 2 hI.he T)⟩

def binaryData {k m} (kind : Fin 4) (R : Source.Formula (k+2)) (w z f j a A _B _C h n Q x y X Y : Fin m) : Formula m :=
  (FormulaCodeRecursiveSyntax.binaryFields kind w a z x y n).conj ((read w h x a f X).conj ((read w h y a f Y).conj (ForcingLogicalCode.binary kind R w a A f j X Y Q)))
theorem binaryData_rename {k m l} (kind : Fin 4) (R : Source.Formula (k+2)) (w z f j a A B C h n Q x y X Y : Fin m) (r : Fin m → Fin l) :
    (binaryData kind R w z f j a A B C h n Q x y X Y).rename r = binaryData kind R (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r h) (r n) (r Q) (r x) (r y) (r X) (r Y) := by
  simp only [binaryData, Formula.rename, FormulaCodeRecursiveSyntax.binaryFields_rename, read_rename, ForcingLogicalCode.binary_rename]
private def binaryBody {k m} (kind : Fin 4) (R : Source.Formula (k+2)) (w z f j a A B C h n Q : Fin m) : Formula (m+4) :=
  binaryData kind R (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 h) (old 4 n) (old 4 Q) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
def binary {k m} (kind : Fin 4) (R : Source.Formula (k+2)) (w z f j a A B C h n Q : Fin m) : Formula m := existsMany 4 (binaryBody kind R w z f j a A B C h n Q)
theorem binary_rename {k m l} (kind : Fin 4) (R : Source.Formula (k+2)) (w z f j a A B C h n Q : Fin m) (r : Fin m → Fin l) :
    (binary kind R w z f j a A B C h n Q).rename r = binary kind R (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r h) (r n) (r Q) := by
  simp only [binary, existsMany_rename, binaryBody, binaryData_rename, lift_old, lift_slot]

private def negativeData {k m} (R : Source.Formula (k+2)) (_H : Source.Formula (k+1)) (w z f j a A _B _C h n Q x X : Fin m) : Formula m :=
  (FormulaCodeRecursiveSyntax.singleFields 4 false w a z x n).conj ((read w h x a f X).conj (ForcingNegCode.compiled R w a A f j X Q))
private theorem negativeData_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x X : Fin m) (r : Fin m → Fin l) :
    (negativeData R H w z f j a A B C h n Q x X).rename r = negativeData R H (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r h) (r n) (r Q) (r x) (r X) := by
  simp only [negativeData, Formula.rename, FormulaCodeRecursiveSyntax.singleFields_rename, read_rename, ForcingNegCode.compiled_rename]
private def negativeBody {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) : Formula (m+2) :=
  negativeData R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 Q) (slot 2 0) (slot 2 1)
def negative {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) : Formula m := existsMany 2 (negativeBody R H w z f j a A B C h n Q)
theorem negative_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) (r : Fin m → Fin l) :
    (negative R H w z f j a A B C h n Q).rename r = negative R H (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r h) (r n) (r Q) := by
  simp only [negative, existsMany_rename, negativeBody, negativeData_rename, lift_old, lift_slot]

private def universalData {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x X : Fin m) : Formula m :=
  (FormulaCodeRecursiveSyntax.singleFields 9 true w a z x n).conj ((read w h x A f X).conj (ForcingLogicalCode.universal R H w a A B C f j X Q))
private theorem universalData_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x X : Fin m) (r : Fin m → Fin l) :
    (universalData R H w z f j a A B C h n Q x X).rename r = universalData R H (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r h) (r n) (r Q) (r x) (r X) := by
  simp only [universalData, Formula.rename, FormulaCodeRecursiveSyntax.singleFields_rename, read_rename, ForcingLogicalCode.universal_rename]
private def universalBody {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) : Formula (m+2) :=
  universalData R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 Q) (slot 2 0) (slot 2 1)
def universal {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) : Formula m := existsMany 2 (universalBody R H w z f j a A B C h n Q)
theorem universal_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) (r : Fin m → Fin l) :
    (universal R H w z f j a A B C h n Q).rename r = universal R H (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r h) (r n) (r Q) := by
  simp only [universal, existsMany_rename, universalBody, universalData_rename, lift_old, lift_slot]

private def existentialData {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x X : Fin m) : Formula m :=
  (FormulaCodeRecursiveSyntax.singleFields 10 true w a z x n).conj ((read w h x A f X).conj (ForcingExistCode.compiled R H w a A B C f j X Q))
private theorem existentialData_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x X : Fin m) (r : Fin m → Fin l) :
    (existentialData R H w z f j a A B C h n Q x X).rename r = existentialData R H (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r h) (r n) (r Q) (r x) (r X) := by
  simp only [existentialData, Formula.rename, FormulaCodeRecursiveSyntax.singleFields_rename, read_rename, ForcingExistCode.compiled_rename]
private def existentialBody {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) : Formula (m+2) :=
  existentialData R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n) (old 2 Q) (slot 2 0) (slot 2 1)
def existential {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) : Formula m := existsMany 2 (existentialBody R H w z f j a A B C h n Q)
theorem existential_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) (r : Fin m → Fin l) :
    (existential R H w z f j a A B C h n Q).rename r = existential R H (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r h) (r n) (r Q) := by
  simp only [existential, existsMany_rename, existentialBody, existentialData_rename, lift_old, lift_slot]

def cases {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) : Formula m :=
  ((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q)).disj ((negative R H w z f j a A B C h n Q).disj ((binary 0 R w z f j a A B C h n Q).disj ((binary 1 R w z f j a A B C h n Q).disj ((binary 2 R w z f j a A B C h n Q).disj ((binary 3 R w z f j a A B C h n Q).disj ((universal R H w z f j a A B C h n Q).disj (existential R H w z f j a A B C h n Q)))))))
def step {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) : Formula m :=
  (formulaCode w n a z).conj (cases R H w z f j a A B C h n Q)
theorem cases_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) (r : Fin m → Fin l) :
    (cases R H w z f j a A B C h n Q).rename r = cases R H (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r h) (r n) (r Q) := by
  simp only [cases, Formula.rename, SyntaxAtomSyntax.atomic_rename, ForcingAtomCode.compiled_rename, negative_rename, binary_rename, universal_rename, existential_rename]
theorem step_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) (r : Fin m → Fin l) :
    (step R H w z f j a A B C h n Q).rename r = step R H (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r h) (r n) (r Q) := by
  simp only [step, Formula.rename, formulaCode_rename, cases_rename]
def existsStep {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n : Fin m) : Formula m := .ex
  (step R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc (Fin.last m))
private theorem existsStep_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n : Fin m) (r : Fin m → Fin l) :
    (existsStep R H w z f j a A B C h n).rename r = existsStep R H (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r h) (r n) := by
  simp only [existsStep, Formula.rename, step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem intro_binary {k m} {Γ : Context m} (kind : Fin 4) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x y X Y : Fin m)
    (hn : Derives Γ (formulaCode w n a z)) (hd : Derives Γ (binaryData kind R w z f j a A B C h n Q x y X Y)) : Derives Γ (step R H w z f j a A B C h n Q) := by
  apply Derives.conjI hn
  have hc : Derives Γ (binary kind R w z f j a A B C h n Q) := by
    apply HornBinderRules.intro_many 4 _ (Fin.cases x (Fin.cases y (SyntaxAtomSyntax.two X Y)))
    exact of_eq (by simp only [binaryBody, binaryData_rename, assign_old, assign_slot]; rfl) hd
  revert hc
  refine Fin.cases ?_ (fun b1 => ?_) kind
  · intro hc
    exact .disjR (.disjR (.disjL hc))
  · refine Fin.cases ?_ (fun b2 => ?_) b1
    · intro hc
      exact .disjR (.disjR (.disjR (.disjL hc)))
    · refine Fin.cases ?_ (fun lastKind => ?_) b2
      · intro hc
        exact .disjR (.disjR (.disjR (.disjR (.disjL hc))))
      · have he : lastKind = 0 := Subsingleton.elim _ _
        subst lastKind
        intro hc
        exact .disjR (.disjR (.disjR (.disjR (.disjR (.disjL hc)))))

private theorem intro_negative {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x X : Fin m)
    (hn : Derives Γ (formulaCode w n a z)) (hd : Derives Γ (negativeData R H w z f j a A B C h n Q x X)) : Derives Γ (step R H w z f j a A B C h n Q) := by
  apply Derives.conjI hn
  have hc : Derives Γ (negative R H w z f j a A B C h n Q) := by
    apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two x X)
    exact of_eq (by simp only [negativeBody, negativeData_rename, assign_old, assign_slot]; rfl) hd
  exact (.disjR (.disjL hc))

private theorem intro_universal {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x X : Fin m)
    (hn : Derives Γ (formulaCode w n a z)) (hd : Derives Γ (universalData R H w z f j a A B C h n Q x X)) : Derives Γ (step R H w z f j a A B C h n Q) := by
  apply Derives.conjI hn
  have hc : Derives Γ (universal R H w z f j a A B C h n Q) := by
    apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two x X)
    exact of_eq (by simp only [universalBody, universalData_rename, assign_old, assign_slot]; rfl) hd
  exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hc)))))))

private theorem intro_existential {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q x X : Fin m)
    (hn : Derives Γ (formulaCode w n a z)) (hd : Derives Γ (existentialData R H w z f j a A B C h n Q x X)) : Derives Γ (step R H w z f j a A B C h n Q) := by
  apply Derives.conjI hn
  have hc : Derives Γ (existential R H w z f j a A B C h n Q) := by
    apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two x X)
    exact of_eq (by simp only [existentialBody, existentialData_rename, assign_old, assign_slot]; rfl) hd
  exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR hc)))))))

theorem source_type {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m)
    (hs : Derives Γ (step R H w z f j a A B C h n Q)) : Derives Γ (formulaCode w n a z) := .conjL hs

private theorem addInputs {k m} {Γ : Context m} {w z f j a A B C h n : Fin m} (hI : Inputs k Γ w z f j a A B C h n) (T : Formula m) :
    Inputs k (Context.add T Γ) w z f j a A B C h n := ⟨add hI.hw T, add hI.hz T, add hI.hf T, add hI.hj T, add hI.hA T, add hI.hB T, add hI.hC T, add hI.he T⟩

private theorem child_at_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x a A z : Fin m)
    (hA : Derives Γ (successor A a)) (hx : Derives Γ (FormulaCodeRecursiveSyntax.advancedCode w x a z)) :
    Derives Γ (formulaCode w x A z) := by
  let T := (successor (Fin.last m) a.castSucc).conj (formulaCode w.castSucc x.castSucc (Fin.last m) z.castSucc)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) hx
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have he := OmegaUniversal.successor_unique (Fin.last m) A.castSucc a.castSucc
    (ZFContext.arithmetic (ZFContext.under hZ T)).base.extensionality (.conjL hT)
    (of_eq (successor_rename A a Fin.castSucc) (under hA T))
  let P := formulaCode w.castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1)) z.castSucc.castSucc
  have ho : Derives Δ (formulaCode w.castSucc x.castSucc A.castSucc z.castSucc) :=
    of_eq (by simp only [P, Formula.instantiate, formulaCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, formulaCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR hT)))
  exact of_eq (formulaCode_rename w x A z Fin.castSucc).symm ho

private theorem binary_stage2 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n x y X Y : Fin m) (hI : Inputs k Γ w z f j a A B C h n)
    (hn : Derives Γ (formulaCode w n a z)) (hd : Derives Γ (FormulaCodeRecursiveSyntax.binaryFields kind w a z x y n))
    (hr0 : Derives Γ (read w h x a f X))
    (hr1 : Derives Γ (read w h y a f Y))
    : Derives Γ (existsStep R H w z f j a A B C h n) := by
  let T := ForcingLogicalCode.binary kind R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc X.castSucc Y.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingLogicalCode.binary_total hZ kind R w a A f j X Y hI.hw hI.hA hI.hf hI.hj (read_type w h x a f X hr0) (read_type w h y a f Y hr1))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have hd1 := of_eq (FormulaCodeRecursiveSyntax.binaryFields_rename kind w a z x y n Fin.castSucc) (under hd T)
  have hr0u := of_eq (read_rename w h x a f X Fin.castSucc) (under hr0 T)
  have hr1u := of_eq (read_rename w h y a f Y Fin.castSucc) (under hr1 T)
  have hb := intro_binary kind R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc (Fin.last m) x.castSucc y.castSucc X.castSucc Y.castSucc hn1
    (.conjI hd1 (.conjI hr0u (.conjI hr1u hT)))
  have ho : Derives Δ (existsStep R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hb
  exact of_eq (existsStep_rename R H w z f j a A B C h n Fin.castSucc).symm ho

private theorem binary_stage1 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n x y X : Fin m) (hI : Inputs k Γ w z f j a A B C h n)
    (hn : Derives Γ (formulaCode w n a z)) (hd : Derives Γ (FormulaCodeRecursiveSyntax.binaryFields kind w a z x y n))
    (hr0 : Derives Γ (read w h x a f X))
    : Derives Γ (existsStep R H w z f j a A B C h n) := by
  let T := read w.castSucc h.castSucc y.castSucc a.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (available_at w z f h n y a hI.he (.conjL (.conjR (.conjR hd))) (.conjR (.conjR (.conjR (.conjR hd)))))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have hd1 := of_eq (FormulaCodeRecursiveSyntax.binaryFields_rename kind w a z x y n Fin.castSucc) (under hd T)
  have hr0u := of_eq (read_rename w h x a f X Fin.castSucc) (under hr0 T)
  have ho := binary_stage2 (ZFContext.under hZ T) kind R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc x.castSucc y.castSucc X.castSucc (Fin.last m) (underInputs hI T) hn1 hd1 hr0u hT
  exact of_eq (existsStep_rename R H w z f j a A B C h n Fin.castSucc).symm ho

private theorem binary_stage0 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n x y : Fin m) (hI : Inputs k Γ w z f j a A B C h n)
    (hn : Derives Γ (formulaCode w n a z)) (hd : Derives Γ (FormulaCodeRecursiveSyntax.binaryFields kind w a z x y n))
    : Derives Γ (existsStep R H w z f j a A B C h n) := by
  let T := read w.castSucc h.castSucc x.castSucc a.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (available_at w z f h n x a hI.he (.conjL (.conjR hd)) (.conjL (.conjR (.conjR (.conjR hd)))))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have hd1 := of_eq (FormulaCodeRecursiveSyntax.binaryFields_rename kind w a z x y n Fin.castSucc) (under hd T)
  have ho := binary_stage1 (ZFContext.under hZ T) kind R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc x.castSucc y.castSucc (Fin.last m) (underInputs hI T) hn1 hd1  hT
  exact of_eq (existsStep_rename R H w z f j a A B C h n Fin.castSucc).symm ho

private theorem binary_case_total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n : Fin m) (hI : Inputs k Γ w z f j a A B C h n)
    (hn : Derives Γ (formulaCode w n a z)) (hc : Derives Γ (FormulaCodeRecursiveSyntax.binaryCase kind w a z n)) :
    Derives Γ (existsStep R H w z f j a A B C h n) := by
  let T := FormulaCodeRecursiveSyntax.binaryCaseBody kind w a z n
  let Δ := Context.add T (raisedContext 2 Γ)
  apply FormulaCodeRecursiveSyntax.eliminate_binary kind w a z n _ hc
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn2 := of_eq (formulaCode_rename w n a z (old 2)) (HornBinderRules.under_body 2 hn T)
  have ho := binary_stage0 (HornBinderRules.zf_body 2 hZ T) kind R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 h) (old 2 n)
    (slot 2 0) (slot 2 1) (underInputs2 hI T) hn2 hT
  exact of_eq (by simp only [Formula.raise, existsStep_rename, old]) ho

private theorem negative_stage1 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n x X : Fin m) (hI : Inputs k Γ w z f j a A B C h n)
    (hn : Derives Γ (formulaCode w n a z)) (hd : Derives Γ (FormulaCodeRecursiveSyntax.singleFields 4 false w a z x n))
    (hr : Derives Γ (read w h x a f X))
    : Derives Γ (existsStep R H w z f j a A B C h n) := by
  let T := ForcingNegCode.compiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc X.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingNegCode.total hZ R w a A f j X hI.hw hI.hA hI.hf hI.hj (read_type w h x a f X hr))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have hd1 := of_eq (FormulaCodeRecursiveSyntax.singleFields_rename 4 false w a z x n Fin.castSucc) (under hd T)
  have hr1 := of_eq (read_rename w h x a f X Fin.castSucc) (under hr T)
  have hb := intro_negative R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc (Fin.last m) x.castSucc X.castSucc hn1 (.conjI hd1 (.conjI hr1 hT))
  have ho : Derives Δ (existsStep R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hb
  exact of_eq (existsStep_rename R H w z f j a A B C h n Fin.castSucc).symm ho

private theorem negative_stage0 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n x : Fin m) (hI : Inputs k Γ w z f j a A B C h n)
    (hn : Derives Γ (formulaCode w n a z)) (hd : Derives Γ (FormulaCodeRecursiveSyntax.singleFields 4 false w a z x n))
    : Derives Γ (existsStep R H w z f j a A B C h n) := by
  have hx : Derives Γ (formulaCode w x a z) := .conjR (.conjR hd)
  let T := read w.castSucc h.castSucc x.castSucc a.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (available_at w z f h n x a hI.he (.conjL (.conjR hd)) hx)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have hd1 := of_eq (FormulaCodeRecursiveSyntax.singleFields_rename 4 false w a z x n Fin.castSucc) (under hd T)
  have ho := negative_stage1 (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc x.castSucc (Fin.last m) (underInputs hI T) hn1 hd1 hT
  exact of_eq (existsStep_rename R H w z f j a A B C h n Fin.castSucc).symm ho

private theorem negative_case_total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n : Fin m) (hI : Inputs k Γ w z f j a A B C h n)
    (hn : Derives Γ (formulaCode w n a z)) (hc : Derives Γ (FormulaCodeRecursiveSyntax.singleCase 4 false w a z n)) :
    Derives Γ (existsStep R H w z f j a A B C h n) := by
  let T := FormulaCodeRecursiveSyntax.singleCaseBody 4 false w a z n
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply FormulaCodeRecursiveSyntax.eliminate_single 4 false w a z n _ hc
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have ho := negative_stage0 (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc (Fin.last m) (underInputs hI T) hn1 hT
  exact of_eq (existsStep_rename R H w z f j a A B C h n Fin.castSucc).symm ho

private theorem universal_stage1 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n x X : Fin m) (hI : Inputs k Γ w z f j a A B C h n)
    (hn : Derives Γ (formulaCode w n a z)) (hd : Derives Γ (FormulaCodeRecursiveSyntax.singleFields 9 true w a z x n))
    (hr : Derives Γ (read w h x A f X))
    : Derives Γ (existsStep R H w z f j a A B C h n) := by
  have ha := Derives.conjL (.conjR (FormulaCodeProperties.guards w n a z hn))
  let T := ForcingLogicalCode.universal R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc X.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingLogicalCode.universal_total hZ R H w a A B C f j X hI.hw ha hI.hA hI.hB hI.hC hI.hf hI.hj (read_type w h x A f X hr))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have hd1 := of_eq (FormulaCodeRecursiveSyntax.singleFields_rename 9 true w a z x n Fin.castSucc) (under hd T)
  have hr1 := of_eq (read_rename w h x A f X Fin.castSucc) (under hr T)
  have hb := intro_universal R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc (Fin.last m) x.castSucc X.castSucc hn1 (.conjI hd1 (.conjI hr1 hT))
  have ho : Derives Δ (existsStep R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hb
  exact of_eq (existsStep_rename R H w z f j a A B C h n Fin.castSucc).symm ho

private theorem universal_stage0 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n x : Fin m) (hI : Inputs k Γ w z f j a A B C h n)
    (hn : Derives Γ (formulaCode w n a z)) (hd : Derives Γ (FormulaCodeRecursiveSyntax.singleFields 9 true w a z x n))
    : Derives Γ (existsStep R H w z f j a A B C h n) := by
  have hx := child_at_successor hZ w x a A z hI.hA (.conjR (.conjR hd))
  let T := read w.castSucc h.castSucc x.castSucc A.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (available_at w z f h n x A hI.he (.conjL (.conjR hd)) hx)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have hd1 := of_eq (FormulaCodeRecursiveSyntax.singleFields_rename 9 true w a z x n Fin.castSucc) (under hd T)
  have ho := universal_stage1 (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc x.castSucc (Fin.last m) (underInputs hI T) hn1 hd1 hT
  exact of_eq (existsStep_rename R H w z f j a A B C h n Fin.castSucc).symm ho

private theorem universal_case_total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n : Fin m) (hI : Inputs k Γ w z f j a A B C h n)
    (hn : Derives Γ (formulaCode w n a z)) (hc : Derives Γ (FormulaCodeRecursiveSyntax.singleCase 9 true w a z n)) :
    Derives Γ (existsStep R H w z f j a A B C h n) := by
  let T := FormulaCodeRecursiveSyntax.singleCaseBody 9 true w a z n
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply FormulaCodeRecursiveSyntax.eliminate_single 9 true w a z n _ hc
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have ho := universal_stage0 (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc (Fin.last m) (underInputs hI T) hn1 hT
  exact of_eq (existsStep_rename R H w z f j a A B C h n Fin.castSucc).symm ho

private theorem existential_stage1 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n x X : Fin m) (hI : Inputs k Γ w z f j a A B C h n)
    (hn : Derives Γ (formulaCode w n a z)) (hd : Derives Γ (FormulaCodeRecursiveSyntax.singleFields 10 true w a z x n))
    (hr : Derives Γ (read w h x A f X))
    : Derives Γ (existsStep R H w z f j a A B C h n) := by
  have ha := Derives.conjL (.conjR (FormulaCodeProperties.guards w n a z hn))
  let T := ForcingExistCode.compiled R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc X.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingExistCode.total hZ R H w a A B C f j X hI.hw ha hI.hA hI.hB hI.hC hI.hf hI.hj (read_type w h x A f X hr))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have hd1 := of_eq (FormulaCodeRecursiveSyntax.singleFields_rename 10 true w a z x n Fin.castSucc) (under hd T)
  have hr1 := of_eq (read_rename w h x A f X Fin.castSucc) (under hr T)
  have hb := intro_existential R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc (Fin.last m) x.castSucc X.castSucc hn1 (.conjI hd1 (.conjI hr1 hT))
  have ho : Derives Δ (existsStep R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hb
  exact of_eq (existsStep_rename R H w z f j a A B C h n Fin.castSucc).symm ho

private theorem existential_stage0 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n x : Fin m) (hI : Inputs k Γ w z f j a A B C h n)
    (hn : Derives Γ (formulaCode w n a z)) (hd : Derives Γ (FormulaCodeRecursiveSyntax.singleFields 10 true w a z x n))
    : Derives Γ (existsStep R H w z f j a A B C h n) := by
  have hx := child_at_successor hZ w x a A z hI.hA (.conjR (.conjR hd))
  let T := read w.castSucc h.castSucc x.castSucc A.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (available_at w z f h n x A hI.he (.conjL (.conjR hd)) hx)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have hd1 := of_eq (FormulaCodeRecursiveSyntax.singleFields_rename 10 true w a z x n Fin.castSucc) (under hd T)
  have ho := existential_stage1 (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc x.castSucc (Fin.last m) (underInputs hI T) hn1 hd1 hT
  exact of_eq (existsStep_rename R H w z f j a A B C h n Fin.castSucc).symm ho

private theorem existential_case_total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n : Fin m) (hI : Inputs k Γ w z f j a A B C h n)
    (hn : Derives Γ (formulaCode w n a z)) (hc : Derives Γ (FormulaCodeRecursiveSyntax.singleCase 10 true w a z n)) :
    Derives Γ (existsStep R H w z f j a A B C h n) := by
  let T := FormulaCodeRecursiveSyntax.singleCaseBody 10 true w a z n
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply FormulaCodeRecursiveSyntax.eliminate_single 10 true w a z n _ hc
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have ho := existential_stage0 (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc (Fin.last m) (underInputs hI T) hn1 hT
  exact of_eq (existsStep_rename R H w z f j a A B C h n Fin.castSucc).symm ho

private theorem atomic_case_total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n : Fin m) (hI : Inputs k Γ w z f j a A B C h n)
    (hn : Derives Γ (formulaCode w n a z)) (hc : Derives Γ (SyntaxAtomSyntax.atomic w a z n)) :
    Derives Γ (existsStep R H w z f j a A B C h n) := by
  let T := ForcingAtomCode.compiled R w.castSucc a.castSucc z.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingAtomCode.total hZ R w a z n hI.hw hI.hz hc)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have hc1 := of_eq (SyntaxAtomSyntax.atomic_rename w a z n Fin.castSucc) (under hc T)
  have hb : Derives Δ (step R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc (Fin.last m)) := .conjI hn1 (.disjL (.conjI hc1 hT))
  have ho : Derives Δ (existsStep R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc h.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hb
  exact of_eq (existsStep_rename R H w z f j a A B C h n Fin.castSucc).symm ho

/-- Full native constructor closure, with actual reads and operation outputs.
Earlier-history availability is the explicit object induction premise. -/
theorem total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j a A B C h n : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (he : Derives Γ (available w z f h n)) (hn : Derives Γ (formulaCode w n a z)) : Derives Γ (existsStep R H w z f j a A B C h n) := by
  have hI : Inputs k Γ w z f j a A B C h n := ⟨hw,hz,hf,hj,hA,hB,hC,he⟩
  have hs : Derives Γ ((FormulaCodeRecursiveSyntax.allCases w n a z).imp (existsStep R H w z f j a A B C h n)) := by
    apply FormulaCodeCaseLogic.all_imp w n a z (existsStep R H w z f j a A B C h n)
    · apply Derives.impI
      exact atomic_case_total (ZFContext.add hZ _) R H w z f j a A B C h n (addInputs hI _) (add hn _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact negative_case_total (ZFContext.add hZ _) R H w z f j a A B C h n (addInputs hI _) (add hn _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case_total (ZFContext.add hZ _) 0 R H w z f j a A B C h n (addInputs hI _) (add hn _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case_total (ZFContext.add hZ _) 1 R H w z f j a A B C h n (addInputs hI _) (add hn _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case_total (ZFContext.add hZ _) 2 R H w z f j a A B C h n (addInputs hI _) (add hn _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case_total (ZFContext.add hZ _) 3 R H w z f j a A B C h n (addInputs hI _) (add hn _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact universal_case_total (ZFContext.add hZ _) R H w z f j a A B C h n (addInputs hI _) (add hn _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact existential_case_total (ZFContext.add hZ _) R H w z f j a A B C h n (addInputs hI _) (add hn _) (.hyp (Or.inl rfl))
  exact .impE hs (.conjR (.impE (.conjL (FormulaCodeRecursive.recursive_iff hZ w n a z hw)) hn))

def sentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((SyntaxNumeralSyntax.numeral (k+2) f).imp ((SyntaxNumeralSyntax.numeral (k+1) j).imp ((successor A a).imp ((successor B A).imp ((successor C B).imp ((available w z f h n).imp ((formulaCode w n a z).imp (existsStep R H w z f j a A B C h n)))))))))).close
theorem kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R H w z f j a A B C h n)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) _) _) _) _) R H w z f j a A B C h n
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

private theorem atomic_type_at {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2))
    (w a z n Q f : Fin m) (hw : Derives Γ (omega w)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hc : Derives Γ (ForcingAtomCode.compiled R w a z n Q)) : Derives Γ (formulaCode w Q a f) := by
  let T := (SyntaxNumeralSyntax.numeral (k+2) (Fin.last m)).conj (formulaCode w.castSucc Q.castSucc a.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingAtomCode.compiled_type hZ R w a z n Q hw hc)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f Fin.castSucc) (under hf T)
  have he := SyntaxNumerals.unique (ZFContext.under hZ T) (k+2) (Fin.last m) f.castSucc (.conjL hT) hf1
  let P := formulaCode w.castSucc.castSucc Q.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1))
  have ho : Derives Δ (formulaCode w.castSucc Q.castSucc a.castSucc f.castSucc) :=
    of_eq (by simp only [P, Formula.instantiate, formulaCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, formulaCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR hT)))
  exact of_eq (formulaCode_rename w Q a f Fin.castSucc).symm ho

private theorem binary_type {k m} {Γ : Context m} (kind : Fin 4) (R : Source.Formula (k+2)) (w z f j a A B C h n Q : Fin m)
    (hc : Derives Γ (binary kind R w z f j a A B C h n Q)) : Derives Γ (formulaCode w Q a f) := by
  let T := binaryBody kind R w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 T _ hc
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ht := ForcingLogicalCode.binary_type kind R (old 4 w) (old 4 a) (old 4 A) (old 4 f) (old 4 j)
    (slot 4 2) (slot 4 3) (old 4 Q) (.conjR (.conjR (.conjR hT)))
  exact of_eq (formulaCode_rename w Q a f (old 4)).symm ht

private theorem negative_type {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m)
    (hc : Derives Γ (negative R H w z f j a A B C h n Q)) : Derives Γ (formulaCode w Q a f) := by
  let T := negativeBody R H w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hc
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ht := ForcingNegCode.compiled_type R (old 2 w) (old 2 a) (old 2 A) (old 2 f) (old 2 j) (slot 2 1) (old 2 Q) (.conjR (.conjR hT))
  exact of_eq (formulaCode_rename w Q a f (old 2)).symm ht

private theorem universal_type {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m)
    (hc : Derives Γ (universal R H w z f j a A B C h n Q)) : Derives Γ (formulaCode w Q a f) := by
  let T := universalBody R H w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hc
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ht := ForcingLogicalCode.universal_type R H (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 f) (old 2 j) (slot 2 1) (old 2 Q) (.conjR (.conjR hT))
  exact of_eq (formulaCode_rename w Q a f (old 2)).symm ht

private theorem existential_type {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m)
    (hc : Derives Γ (existential R H w z f j a A B C h n Q)) : Derives Γ (formulaCode w Q a f) := by
  let T := existentialBody R H w z f j a A B C h n Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hc
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ht := ForcingExistCode.compiled_type R H (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 f) (old 2 j) (slot 2 1) (old 2 Q) (.conjR (.conjR hT))
  exact of_eq (formulaCode_rename w Q a f (old 2)).symm ht

private theorem cases_imp {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) (P : Formula m)
    (h0 : Derives Γ (((SyntaxAtomSyntax.atomic w a z n).conj (ForcingAtomCode.compiled R w a z n Q)).imp P))
    (h1 : Derives Γ ((negative R H w z f j a A B C h n Q).imp P))
    (h2 : Derives Γ ((binary 0 R w z f j a A B C h n Q).imp P))
    (h3 : Derives Γ ((binary 1 R w z f j a A B C h n Q).imp P))
    (h4 : Derives Γ ((binary 2 R w z f j a A B C h n Q).imp P))
    (h5 : Derives Γ ((binary 3 R w z f j a A B C h n Q).imp P))
    (h6 : Derives Γ ((universal R H w z f j a A B C h n Q).imp P))
    (h7 : Derives Γ ((existential R H w z f j a A B C h n Q).imp P))
    : Derives Γ ((cases R H w z f j a A B C h n Q).imp P) := (FormulaCodeCaseLogic.disj_imp h0 (FormulaCodeCaseLogic.disj_imp h1 (FormulaCodeCaseLogic.disj_imp h2 (FormulaCodeCaseLogic.disj_imp h3 (FormulaCodeCaseLogic.disj_imp h4 (FormulaCodeCaseLogic.disj_imp h5 (FormulaCodeCaseLogic.disj_imp h6 h7)))))))

theorem target_type {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j a A B C h n Q : Fin m) (hw : Derives Γ (omega w)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hs : Derives Γ (step R H w z f j a A B C h n Q)) : Derives Γ (formulaCode w Q a f) := by
  have hi : Derives Γ ((cases R H w z f j a A B C h n Q).imp (formulaCode w Q a f)) := by
    apply cases_imp R H w z f j a A B C h n Q (formulaCode w Q a f)
    · apply Derives.impI
      exact atomic_type_at (ZFContext.add hZ _) R w a z n Q f (add hw _) (add hf _) (.conjR (.hyp (Or.inl rfl)))
    · apply Derives.impI
      exact negative_type R H w z f j a A B C h n Q (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_type 0 R w z f j a A B C h n Q (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_type 1 R w z f j a A B C h n Q (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_type 2 R w z f j a A B C h n Q (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_type 3 R w z f j a A B C h n Q (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact universal_type R H w z f j a A B C h n Q (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact existential_type R H w z f j a A B C h n Q (.hyp (Or.inl rfl))
  exact .impE hi (.conjR hs)

def existsState {m} (w a f Q : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (state w.castSucc a.castSucc f.castSucc Q.castSucc (Fin.last m)))
theorem state_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a f Q : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (formulaCode w Q a f)) : Derives Γ (existsState w a f Q) := by
  have hg := FormulaCodeProperties.guards w Q a f ht
  have hi : Derives Γ (SyntaxForestSyntax.inputs 2 w (SyntaxAtomSyntax.two a Q)) :=
    .conjI (.conjL (.conjR hg)) (.conjI (.conjL hg) (.eqRefl w))
  let T := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxForestSyntax.forest 2 w.castSucc (SyntaxAtomSyntax.two a.castSucc Q.castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (SyntaxForests.exists_forest hZ 2 w (SyntaxAtomSyntax.two a Q) hw hi)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ht1 := of_eq (formulaCode_rename w Q a f Fin.castSucc) (under ht T)
  have ho : Derives Δ (existsState w.castSucc a.castSucc f.castSucc Q.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [state, Formula.instantiate, Formula.rename,
      SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map, formulaCode_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjL hT) (.conjI (.conjR hT) ht1))
  exact of_eq (by simp only [existsState, Formula.rename, state_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

theorem intro_read {m} {Γ : Context m} (w h x a f Q v t : Fin m)
    (hv : Derives Γ (GraphSyntax.edge h x v)) (ht : Derives Γ (.mem t v)) (hs : Derives Γ (state w a f Q t)) :
    Derives Γ (read w h x a f Q) := by
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two v t)
  exact of_eq (by simp only [Formula.rename, GraphSyntax.edge_rename, state_rename, assign_old, assign_slot]; rfl)
    (.conjI hv (.conjI ht hs))

theorem state_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a f Q b g V t : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (state w a f Q t)) (ht : Derives Γ (state w b g V t)) :
    Derives Γ ((Formula.equal a b).conj (.equal Q V)) := .conjI
  (SyntaxForestInjective.input_eq hZ 2 w (SyntaxAtomSyntax.two a Q) (SyntaxAtomSyntax.two b V) t 0 hw (.conjL hs) (.conjL ht))
  (SyntaxForestInjective.input_eq hZ 2 w (SyntaxAtomSyntax.two a Q) (SyntaxAtomSyntax.two b V) t 1 hw (.conjL hs) (.conjL ht))

def typeSentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) : Source.Sentence :=
  ((omega w).imp ((SyntaxNumeralSyntax.numeral (k+2) f).imp ((step R H w z f j a A B C h n Q).imp (formulaCode w Q a f)))).close
theorem type_kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C h n Q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (typeSentence R H w z f j a A B C h n Q)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact target_type (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) R H w z f j a A B C h n Q
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingCodeStep
