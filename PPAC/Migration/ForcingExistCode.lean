import PPAC.Migration.ForcingExistChildCode
import PPAC.Migration.ForcingExistGuardsCode
import PPAC.Migration.Internal.FormulaCodeConstructors

/-! The complete literal existential branch of pinned AtomicData.Force and
ForcingFormula.basic: ALL q (q in P -> (R(q,p) -> EX r (r in P AND
(R(r,q) AND EX x (H(x) AND child[v plus x,p:=r]))))). All codes, environments,
heads and constructor executions are produced under object EX. This is one
step on an already interpreted arbitrary internal child code, not the full
raw interpreter, uniform axiom correctness, proof reduction or final Con. -/
namespace PPAC.Migration.ForcingExistCode
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeConstructSyntax (typedAt typedAt_rename)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
set_option maxRecDepth 16384

private def binAt {m} (tag : Nat) (w b f x y Q : Fin m) : Formula m :=
  typedAt 2 tag w (SyntaxAtomSyntax.two x y) Q b f
private def quantAt {m} (tag : Nat) (w b f x Q : Fin m) : Formula m :=
  typedAt 1 tag w (fun _ => x) Q b f
private theorem binAt_rename {m l} (tag : Nat) (w b f x y Q : Fin m) (r : Fin m → Fin l) :
    (binAt tag w b f x y Q).rename r = binAt tag (r w) (r b) (r f) (r x) (r y) (r Q) := by
  simp only [binAt, typedAt_rename, SyntaxAtomSyntax.two_map]
private theorem quantAt_rename {m l} (tag : Nat) (w b f x Q : Fin m) (r : Fin m → Fin l) :
    (quantAt tag w b f x Q).rename r = quantAt tag (r w) (r b) (r f) (r x) (r Q) := by
  simp only [quantAt, typedAt_rename]

private def shellData {m} (w a A B C f qM qO rM rO D Nc Q : Fin m) (v : Fin 7 → Fin m) : Formula m :=
  (binAt 5 w C f D Nc (v 0)).conj ((quantAt 10 w B f (v 0) (v 1)).conj ((binAt 5 w B f rO (v 1) (v 2)).conj ((binAt 5 w B f rM (v 2) (v 3)).conj ((quantAt 10 w A f (v 3) (v 4)).conj ((binAt 7 w A f qO (v 4) (v 5)).conj ((binAt 7 w A f qM (v 5) (v 6)).conj (quantAt 9 w a f (v 6) Q)))))))
private theorem shellData_rename {m l} (w a A B C f qM qO rM rO D Nc Q : Fin m) (v : Fin 7 → Fin m) (r : Fin m → Fin l) :
    (shellData w a A B C f qM qO rM rO D Nc Q v).rename r = shellData (r w) (r a) (r A) (r B) (r C) (r f) (r qM) (r qO) (r rM) (r rO) (r D) (r Nc) (r Q) (fun i => r (v i)) := by
  simp only [shellData, Formula.rename, binAt_rename, quantAt_rename]
private def shellBody {m} (w a A B C f qM qO rM rO D Nc Q : Fin m) : Formula (m+7) :=
  shellData (old 7 w) (old 7 a) (old 7 A) (old 7 B) (old 7 C) (old 7 f) (old 7 qM) (old 7 qO) (old 7 rM) (old 7 rO) (old 7 D) (old 7 Nc) (old 7 Q) (slot 7)
private def shell {m} (w a A B C f qM qO rM rO D Nc Q : Fin m) : Formula m := existsMany 7 (shellBody w a A B C f qM qO rM rO D Nc Q)
private theorem shell_rename {m l} (w a A B C f qM qO rM rO D Nc Q : Fin m) (r : Fin m → Fin l) :
    (shell w a A B C f qM qO rM rO D Nc Q).rename r = shell (r w) (r a) (r A) (r B) (r C) (r f) (r qM) (r qO) (r rM) (r rO) (r D) (r Nc) (r Q) := by
  simp only [shell, existsMany_rename, shellBody, shellData_rename, lift_old, lift_slot]
private def existsShell {m} (w a A B C f qM qO rM rO D Nc : Fin m) : Formula m := .ex
  (shell w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc qM.castSucc qO.castSucc rM.castSucc rO.castSucc D.castSucc Nc.castSucc (Fin.last m))
private theorem existsShell_rename {m l} (w a A B C f qM qO rM rO D Nc : Fin m) (r : Fin m → Fin l) :
    (existsShell w a A B C f qM qO rM rO D Nc).rename r = existsShell (r w) (r a) (r A) (r B) (r C) (r f) (r qM) (r qO) (r rM) (r rO) (r D) (r Nc) := by
  simp only [existsShell, Formula.rename, shell_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private structure ShellInputs {m} (Γ : Context m) (w a A B C f qM qO rM rO D Nc : Fin m) : Prop where
  hw : Derives Γ (omega w)
  hA : Derives Γ (successor A a)
  hB : Derives Γ (successor B A)
  hC : Derives Γ (successor C B)
  ca : Derives Γ (SyntaxTermSyntax.contexts w a f)
  cA : Derives Γ (SyntaxTermSyntax.contexts w A f)
  cB : Derives Γ (SyntaxTermSyntax.contexts w B f)
  cC : Derives Γ (SyntaxTermSyntax.contexts w C f)
  m : Derives Γ (formulaCode w qM A f)
  o : Derives Γ (formulaCode w qO A f)
  r : Derives Γ (formulaCode w rM B f)
  s : Derives Γ (formulaCode w rO B f)
  d : Derives Γ (formulaCode w D C f)
  c : Derives Γ (formulaCode w Nc C f)
private theorem underShell {m} {Γ : Context m} {w a A B C f qM qO rM rO D Nc : Fin m}
    (h : ShellInputs Γ w a A B C f qM qO rM rO D Nc) (T : Formula (m+1)) :
    ShellInputs (Context.add T (Context.image Formula.raise Γ)) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc qM.castSucc qO.castSucc rM.castSucc rO.castSucc D.castSucc Nc.castSucc := by
  exact ⟨of_eq (omega_rename w Fin.castSucc) (under h.hw T),
    of_eq (successor_rename A a Fin.castSucc) (under h.hA T),
    of_eq (successor_rename B A Fin.castSucc) (under h.hB T),
    of_eq (successor_rename C B Fin.castSucc) (under h.hC T),
    of_eq (SyntaxTermSyntax.contexts_rename w a f Fin.castSucc) (under h.ca T),
    of_eq (SyntaxTermSyntax.contexts_rename w A f Fin.castSucc) (under h.cA T),
    of_eq (SyntaxTermSyntax.contexts_rename w B f Fin.castSucc) (under h.cB T),
    of_eq (SyntaxTermSyntax.contexts_rename w C f Fin.castSucc) (under h.cC T),
    of_eq (formulaCode_rename w qM A f Fin.castSucc) (under h.m T),
    of_eq (formulaCode_rename w qO A f Fin.castSucc) (under h.o T),
    of_eq (formulaCode_rename w rM B f Fin.castSucc) (under h.r T),
    of_eq (formulaCode_rename w rO B f Fin.castSucc) (under h.s T),
    of_eq (formulaCode_rename w D C f Fin.castSucc) (under h.d T),
    of_eq (formulaCode_rename w Nc C f Fin.castSucc) (under h.c T)⟩

private theorem shell_stage7 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f qM qO rM rO D Nc x0 x1 x2 x3 x4 x5 x6 : Fin m) (h : ShellInputs Γ w a A B C f qM qO rM rO D Nc)
    (h0 : Derives Γ (binAt 5 w C f D Nc x0))
    (h1 : Derives Γ (quantAt 10 w B f x0 x1))
    (h2 : Derives Γ (binAt 5 w B f rO x1 x2))
    (h3 : Derives Γ (binAt 5 w B f rM x2 x3))
    (h4 : Derives Γ (quantAt 10 w A f x3 x4))
    (h5 : Derives Γ (binAt 7 w A f qO x4 x5))
    (h6 : Derives Γ (binAt 7 w A f qM x5 x6))
    : Derives Γ (existsShell w a A B C f qM qO rM rO D Nc) := by
  have he := FormulaCodeConstruct.exists_of_fiber 1 9 w (fun _ => x6) a f
    (FormulaCodeConstructors.universal hZ w a f x6 h.hw
      (.conjI h.ca (FormulaCodeRecursiveSyntax.intro_advanced w x6 a f A h.hA (.conjR h6))))
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (quantAt 9 w.castSucc a.castSucc f.castSucc x6.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (binAt_rename 5 w C f D Nc x0 Fin.castSucc) (under h0 T)
  have h1u := of_eq (quantAt_rename 10 w B f x0 x1 Fin.castSucc) (under h1 T)
  have h2u := of_eq (binAt_rename 5 w B f rO x1 x2 Fin.castSucc) (under h2 T)
  have h3u := of_eq (binAt_rename 5 w B f rM x2 x3 Fin.castSucc) (under h3 T)
  have h4u := of_eq (quantAt_rename 10 w A f x3 x4 Fin.castSucc) (under h4 T)
  have h5u := of_eq (binAt_rename 7 w A f qO x4 x5 Fin.castSucc) (under h5 T)
  have h6u := of_eq (binAt_rename 7 w A f qM x5 x6 Fin.castSucc) (under h6 T)
  let v : Fin 7 → Fin (m+1) := Fin.cases x0.castSucc (Fin.cases x1.castSucc (Fin.cases x2.castSucc (Fin.cases x3.castSucc (Fin.cases x4.castSucc (Fin.cases x5.castSucc (Fin.cases x6.castSucc (fun i => Fin.elim0 i)))))))
  have hd : Derives Δ (shellData w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc qM.castSucc qO.castSucc rM.castSucc rO.castSucc D.castSucc Nc.castSucc (Fin.last m) v) :=
    (.conjI h0u (.conjI h1u (.conjI h2u (.conjI h3u (.conjI h4u (.conjI h5u (.conjI h6u (.conjR hT))))))))
  have hb : Derives Δ (shell w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc qM.castSucc qO.castSucc rM.castSucc rO.castSucc D.castSucc Nc.castSucc (Fin.last m)) := by
    apply HornBinderRules.intro_many 7 _ v
    exact of_eq (by simp only [shellBody, shellData_rename, assign_old, assign_slot]) hd
  have ho : Derives Δ (existsShell w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc qM.castSucc qO.castSucc rM.castSucc rO.castSucc D.castSucc Nc.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hb
  exact of_eq (existsShell_rename w a A B C f qM qO rM rO D Nc Fin.castSucc).symm ho

private theorem shell_stage6 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f qM qO rM rO D Nc x0 x1 x2 x3 x4 x5 : Fin m) (h : ShellInputs Γ w a A B C f qM qO rM rO D Nc)
    (h0 : Derives Γ (binAt 5 w C f D Nc x0))
    (h1 : Derives Γ (quantAt 10 w B f x0 x1))
    (h2 : Derives Γ (binAt 5 w B f rO x1 x2))
    (h3 : Derives Γ (binAt 5 w B f rM x2 x3))
    (h4 : Derives Γ (quantAt 10 w A f x3 x4))
    (h5 : Derives Γ (binAt 7 w A f qO x4 x5))
    : Derives Γ (existsShell w a A B C f qM qO rM rO D Nc) := by
  have he := FormulaCodeConstruct.exists_of_fiber 2 7 w (SyntaxAtomSyntax.two qM x5) A f
    (FormulaCodeConstructors.binary2 hZ w A f qM x5 h.hw
      (.conjI h.cA (.conjI h.m (.conjR h5))))
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (binAt 7 w.castSucc A.castSucc f.castSucc qM.castSucc x5.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (binAt_rename 5 w C f D Nc x0 Fin.castSucc) (under h0 T)
  have h1u := of_eq (quantAt_rename 10 w B f x0 x1 Fin.castSucc) (under h1 T)
  have h2u := of_eq (binAt_rename 5 w B f rO x1 x2 Fin.castSucc) (under h2 T)
  have h3u := of_eq (binAt_rename 5 w B f rM x2 x3 Fin.castSucc) (under h3 T)
  have h4u := of_eq (quantAt_rename 10 w A f x3 x4 Fin.castSucc) (under h4 T)
  have h5u := of_eq (binAt_rename 7 w A f qO x4 x5 Fin.castSucc) (under h5 T)
  have ho := shell_stage7 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc qM.castSucc qO.castSucc rM.castSucc rO.castSucc D.castSucc Nc.castSucc x0.castSucc x1.castSucc x2.castSucc x3.castSucc x4.castSucc x5.castSucc (Fin.last m) (underShell h T) h0u h1u h2u h3u h4u h5u (.conjR hT)
  exact of_eq (existsShell_rename w a A B C f qM qO rM rO D Nc Fin.castSucc).symm ho

private theorem shell_stage5 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f qM qO rM rO D Nc x0 x1 x2 x3 x4 : Fin m) (h : ShellInputs Γ w a A B C f qM qO rM rO D Nc)
    (h0 : Derives Γ (binAt 5 w C f D Nc x0))
    (h1 : Derives Γ (quantAt 10 w B f x0 x1))
    (h2 : Derives Γ (binAt 5 w B f rO x1 x2))
    (h3 : Derives Γ (binAt 5 w B f rM x2 x3))
    (h4 : Derives Γ (quantAt 10 w A f x3 x4))
    : Derives Γ (existsShell w a A B C f qM qO rM rO D Nc) := by
  have he := FormulaCodeConstruct.exists_of_fiber 2 7 w (SyntaxAtomSyntax.two qO x4) A f
    (FormulaCodeConstructors.binary2 hZ w A f qO x4 h.hw
      (.conjI h.cA (.conjI h.o (.conjR h4))))
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (binAt 7 w.castSucc A.castSucc f.castSucc qO.castSucc x4.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (binAt_rename 5 w C f D Nc x0 Fin.castSucc) (under h0 T)
  have h1u := of_eq (quantAt_rename 10 w B f x0 x1 Fin.castSucc) (under h1 T)
  have h2u := of_eq (binAt_rename 5 w B f rO x1 x2 Fin.castSucc) (under h2 T)
  have h3u := of_eq (binAt_rename 5 w B f rM x2 x3 Fin.castSucc) (under h3 T)
  have h4u := of_eq (quantAt_rename 10 w A f x3 x4 Fin.castSucc) (under h4 T)
  have ho := shell_stage6 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc qM.castSucc qO.castSucc rM.castSucc rO.castSucc D.castSucc Nc.castSucc x0.castSucc x1.castSucc x2.castSucc x3.castSucc x4.castSucc (Fin.last m) (underShell h T) h0u h1u h2u h3u h4u (.conjR hT)
  exact of_eq (existsShell_rename w a A B C f qM qO rM rO D Nc Fin.castSucc).symm ho

private theorem shell_stage4 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f qM qO rM rO D Nc x0 x1 x2 x3 : Fin m) (h : ShellInputs Γ w a A B C f qM qO rM rO D Nc)
    (h0 : Derives Γ (binAt 5 w C f D Nc x0))
    (h1 : Derives Γ (quantAt 10 w B f x0 x1))
    (h2 : Derives Γ (binAt 5 w B f rO x1 x2))
    (h3 : Derives Γ (binAt 5 w B f rM x2 x3))
    : Derives Γ (existsShell w a A B C f qM qO rM rO D Nc) := by
  have he := FormulaCodeConstruct.exists_of_fiber 1 10 w (fun _ => x3) A f
    (FormulaCodeConstructors.existential hZ w A f x3 h.hw
      (.conjI h.cA (FormulaCodeRecursiveSyntax.intro_advanced w x3 A f B h.hB (.conjR h3))))
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (quantAt 10 w.castSucc A.castSucc f.castSucc x3.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (binAt_rename 5 w C f D Nc x0 Fin.castSucc) (under h0 T)
  have h1u := of_eq (quantAt_rename 10 w B f x0 x1 Fin.castSucc) (under h1 T)
  have h2u := of_eq (binAt_rename 5 w B f rO x1 x2 Fin.castSucc) (under h2 T)
  have h3u := of_eq (binAt_rename 5 w B f rM x2 x3 Fin.castSucc) (under h3 T)
  have ho := shell_stage5 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc qM.castSucc qO.castSucc rM.castSucc rO.castSucc D.castSucc Nc.castSucc x0.castSucc x1.castSucc x2.castSucc x3.castSucc (Fin.last m) (underShell h T) h0u h1u h2u h3u (.conjR hT)
  exact of_eq (existsShell_rename w a A B C f qM qO rM rO D Nc Fin.castSucc).symm ho

private theorem shell_stage3 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f qM qO rM rO D Nc x0 x1 x2 : Fin m) (h : ShellInputs Γ w a A B C f qM qO rM rO D Nc)
    (h0 : Derives Γ (binAt 5 w C f D Nc x0))
    (h1 : Derives Γ (quantAt 10 w B f x0 x1))
    (h2 : Derives Γ (binAt 5 w B f rO x1 x2))
    : Derives Γ (existsShell w a A B C f qM qO rM rO D Nc) := by
  have he := FormulaCodeConstruct.exists_of_fiber 2 5 w (SyntaxAtomSyntax.two rM x2) B f
    (FormulaCodeConstructors.binary0 hZ w B f rM x2 h.hw
      (.conjI h.cB (.conjI h.r (.conjR h2))))
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (binAt 5 w.castSucc B.castSucc f.castSucc rM.castSucc x2.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (binAt_rename 5 w C f D Nc x0 Fin.castSucc) (under h0 T)
  have h1u := of_eq (quantAt_rename 10 w B f x0 x1 Fin.castSucc) (under h1 T)
  have h2u := of_eq (binAt_rename 5 w B f rO x1 x2 Fin.castSucc) (under h2 T)
  have ho := shell_stage4 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc qM.castSucc qO.castSucc rM.castSucc rO.castSucc D.castSucc Nc.castSucc x0.castSucc x1.castSucc x2.castSucc (Fin.last m) (underShell h T) h0u h1u h2u (.conjR hT)
  exact of_eq (existsShell_rename w a A B C f qM qO rM rO D Nc Fin.castSucc).symm ho

private theorem shell_stage2 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f qM qO rM rO D Nc x0 x1 : Fin m) (h : ShellInputs Γ w a A B C f qM qO rM rO D Nc)
    (h0 : Derives Γ (binAt 5 w C f D Nc x0))
    (h1 : Derives Γ (quantAt 10 w B f x0 x1))
    : Derives Γ (existsShell w a A B C f qM qO rM rO D Nc) := by
  have he := FormulaCodeConstruct.exists_of_fiber 2 5 w (SyntaxAtomSyntax.two rO x1) B f
    (FormulaCodeConstructors.binary0 hZ w B f rO x1 h.hw
      (.conjI h.cB (.conjI h.s (.conjR h1))))
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (binAt 5 w.castSucc B.castSucc f.castSucc rO.castSucc x1.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (binAt_rename 5 w C f D Nc x0 Fin.castSucc) (under h0 T)
  have h1u := of_eq (quantAt_rename 10 w B f x0 x1 Fin.castSucc) (under h1 T)
  have ho := shell_stage3 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc qM.castSucc qO.castSucc rM.castSucc rO.castSucc D.castSucc Nc.castSucc x0.castSucc x1.castSucc (Fin.last m) (underShell h T) h0u h1u (.conjR hT)
  exact of_eq (existsShell_rename w a A B C f qM qO rM rO D Nc Fin.castSucc).symm ho

private theorem shell_stage1 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f qM qO rM rO D Nc x0 : Fin m) (h : ShellInputs Γ w a A B C f qM qO rM rO D Nc)
    (h0 : Derives Γ (binAt 5 w C f D Nc x0))
    : Derives Γ (existsShell w a A B C f qM qO rM rO D Nc) := by
  have he := FormulaCodeConstruct.exists_of_fiber 1 10 w (fun _ => x0) B f
    (FormulaCodeConstructors.existential hZ w B f x0 h.hw
      (.conjI h.cB (FormulaCodeRecursiveSyntax.intro_advanced w x0 B f C h.hC (.conjR h0))))
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (quantAt 10 w.castSucc B.castSucc f.castSucc x0.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (binAt_rename 5 w C f D Nc x0 Fin.castSucc) (under h0 T)
  have ho := shell_stage2 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc qM.castSucc qO.castSucc rM.castSucc rO.castSucc D.castSucc Nc.castSucc x0.castSucc (Fin.last m) (underShell h T) h0u (.conjR hT)
  exact of_eq (existsShell_rename w a A B C f qM qO rM rO D Nc Fin.castSucc).symm ho

private theorem shell_stage0 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f qM qO rM rO D Nc : Fin m) (h : ShellInputs Γ w a A B C f qM qO rM rO D Nc)
    : Derives Γ (existsShell w a A B C f qM qO rM rO D Nc) := by
  have he := FormulaCodeConstruct.exists_of_fiber 2 5 w (SyntaxAtomSyntax.two D Nc) C f
    (FormulaCodeConstructors.binary0 hZ w C f D Nc h.hw
      (.conjI h.cC (.conjI h.d h.c)))
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (binAt 5 w.castSucc C.castSucc f.castSucc D.castSucc Nc.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ho := shell_stage1 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc qM.castSucc qO.castSucc rM.castSucc rO.castSucc D.castSucc Nc.castSucc (Fin.last m) (underShell h T)  (.conjR hT)
  exact of_eq (existsShell_rename w a A B C f qM qO rM rO D Nc Fin.castSucc).symm ho

private theorem shell_type {m} {Γ : Context m} (w a A B C f qM qO rM rO D Nc Q : Fin m)
    (h : Derives Γ (shell w a A B C f qM qO rM rO D Nc Q)) : Derives Γ (formulaCode w Q a f) := by
  let T := shellBody w a A B C f qM qO rM rO D Nc Q
  let Δ := Context.add T (raisedContext 7 Γ)
  apply HornBinderRules.eliminate_many 7 T _ h
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w Q a f (old 7)).symm (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hT))))))))

private theorem bin_inputs_subst {m} {Γ : Context m} (tag : Nat) (w b f x y Q X Y : Fin m)
    (hx : Derives Γ (.equal x X))
    (hy : Derives Γ (.equal y Y))
    (h : Derives Γ (binAt tag w b f x y Q)) : Derives Γ (binAt tag w b f X Y Q) := by
  let P0 := binAt tag w.castSucc b.castSucc f.castSucc (Fin.last m) y.castSucc Q.castSucc
  have h0 : Derives Γ (binAt tag w b f X y Q) :=
    of_eq (by simp only [P0, Formula.instantiate, binAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P0 hx (of_eq (by simp only [P0, Formula.instantiate, binAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  let P1 := binAt tag w.castSucc b.castSucc f.castSucc X.castSucc (Fin.last m) Q.castSucc
  have h1 : Derives Γ (binAt tag w b f X Y Q) :=
    of_eq (by simp only [P1, Formula.instantiate, binAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P1 hy (of_eq (by simp only [P1, Formula.instantiate, binAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h0))
  exact h1

private theorem quant_inputs_subst {m} {Γ : Context m} (tag : Nat) (w b f x Q X : Fin m)
    (hx : Derives Γ (.equal x X))
    (h : Derives Γ (quantAt tag w b f x Q)) : Derives Γ (quantAt tag w b f X Q) := by
  let P0 := quantAt tag w.castSucc b.castSucc f.castSucc (Fin.last m) Q.castSucc
  have h0 : Derives Γ (quantAt tag w b f X Q) :=
    of_eq (by simp only [P0, Formula.instantiate, quantAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P0 hx (of_eq (by simp only [P0, Formula.instantiate, quantAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  exact h0

private theorem shellData_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f qM qO rM rO D Nc Q V : Fin m) (xs ys : Fin 7 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (shellData w a A B C f qM qO rM rO D Nc Q xs)) (hy : Derives Γ (shellData w a A B C f qM qO rM rO D Nc V ys)) : Derives Γ (.equal Q V) := by
  have e0 := SyntaxConstructors.unique hZ 2 5 w (SyntaxAtomSyntax.two D Nc) (xs 0) (ys 0) hw (.conjL (.conjL hx)) (.conjL (.conjL hy))
  have h1 := quant_inputs_subst 10 w B f (xs 0) (xs 1) (ys 0) e0 (.conjL (.conjR hx))
  have e1 := SyntaxConstructors.unique hZ 1 10 w (fun _ => (ys 0)) (xs 1) (ys 1) hw (.conjL h1) (.conjL (.conjL (.conjR hy)))
  have h2 := bin_inputs_subst 5 w B f rO (xs 1) (xs 2) rO (ys 1) (.eqRefl rO) e1 (.conjL (.conjR (.conjR hx)))
  have e2 := SyntaxConstructors.unique hZ 2 5 w (SyntaxAtomSyntax.two rO (ys 1)) (xs 2) (ys 2) hw (.conjL h2) (.conjL (.conjL (.conjR (.conjR hy))))
  have h3 := bin_inputs_subst 5 w B f rM (xs 2) (xs 3) rM (ys 2) (.eqRefl rM) e2 (.conjL (.conjR (.conjR (.conjR hx))))
  have e3 := SyntaxConstructors.unique hZ 2 5 w (SyntaxAtomSyntax.two rM (ys 2)) (xs 3) (ys 3) hw (.conjL h3) (.conjL (.conjL (.conjR (.conjR (.conjR hy)))))
  have h4 := quant_inputs_subst 10 w A f (xs 3) (xs 4) (ys 3) e3 (.conjL (.conjR (.conjR (.conjR (.conjR hx)))))
  have e4 := SyntaxConstructors.unique hZ 1 10 w (fun _ => (ys 3)) (xs 4) (ys 4) hw (.conjL h4) (.conjL (.conjL (.conjR (.conjR (.conjR (.conjR hy))))))
  have h5 := bin_inputs_subst 7 w A f qO (xs 4) (xs 5) qO (ys 4) (.eqRefl qO) e4 (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hx))))))
  have e5 := SyntaxConstructors.unique hZ 2 7 w (SyntaxAtomSyntax.two qO (ys 4)) (xs 5) (ys 5) hw (.conjL h5) (.conjL (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hy)))))))
  have h6 := bin_inputs_subst 7 w A f qM (xs 5) (xs 6) qM (ys 5) (.eqRefl qM) e5 (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hx)))))))
  have e6 := SyntaxConstructors.unique hZ 2 7 w (SyntaxAtomSyntax.two qM (ys 5)) (xs 6) (ys 6) hw (.conjL h6) (.conjL (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hy))))))))
  have h7 := quant_inputs_subst 9 w a f (xs 6) Q (ys 6) e6 (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hx)))))))
  have e7 := SyntaxConstructors.unique hZ 1 9 w (fun _ => (ys 6)) Q V hw (.conjL h7) (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hy))))))))
  exact e7

private theorem shell_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f qM qO rM rO D Nc Q V : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (shell w a A B C f qM qO rM rO D Nc Q)) (hv : Derives Γ (shell w a A B C f qM qO rM rO D Nc V)) : Derives Γ (.equal Q V) := by
  let T := shellBody w a A B C f qM qO rM rO D Nc Q
  let Δ := Context.add T (raisedContext 7 Γ)
  apply HornBinderRules.eliminate_many 7 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hv1 := of_eq (shell_rename w a A B C f qM qO rM rO D Nc V (old 7)) (HornBinderRules.under_body 7 hv T)
  let U := shellBody (old 7 w) (old 7 a) (old 7 A) (old 7 B) (old 7 C) (old 7 f) (old 7 qM) (old 7 qO) (old 7 rM) (old 7 rO) (old 7 D) (old 7 Nc) (old 7 V)
  let Ξ := Context.add U (raisedContext 7 Δ)
  apply HornBinderRules.eliminate_many 7 U _ hv1
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hw2 : Derives Ξ (omega (old 7 (old 7 w))) := of_eq (by simp only [omega_rename])
    (HornBinderRules.under_body 7 (HornBinderRules.under_body 7 hw T) U)
  have hx2 : Derives Ξ (shellData (old 7 (old 7 w)) (old 7 (old 7 a)) (old 7 (old 7 A)) (old 7 (old 7 B)) (old 7 (old 7 C)) (old 7 (old 7 f)) (old 7 (old 7 qM)) (old 7 (old 7 qO)) (old 7 (old 7 rM)) (old 7 (old 7 rO)) (old 7 (old 7 D)) (old 7 (old 7 Nc)) (old 7 (old 7 Q)) (fun i => old 7 (slot 7 i))) :=
    of_eq (by simp only [T, shellBody, shellData_rename]) (HornBinderRules.under_body 7 hT U)
  exact shellData_unique (HornBinderRules.zf_body 7 (HornBinderRules.zf_body 7 hZ T) U)
    (old 7 (old 7 w)) (old 7 (old 7 a)) (old 7 (old 7 A)) (old 7 (old 7 B)) (old 7 (old 7 C)) (old 7 (old 7 f)) (old 7 (old 7 qM)) (old 7 (old 7 qO)) (old 7 (old 7 rM)) (old 7 (old 7 rO)) (old 7 (old 7 D)) (old 7 (old 7 Nc)) (old 7 (old 7 Q)) (old 7 (old 7 V))
    (fun i => old 7 (slot 7 i)) (slot 7) hw2 hx2 hU

private def data {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m) (v : Fin 8 → Fin m) : Formula m :=
  (SyntaxMixedImageHead.head w C f (v 0) (v 1)).conj ((ForcingGuardCode.compiled false R w A f (v 1) (v 2)).conj ((ForcingGuardCode.compiled true R w A f (v 1) (v 3)).conj ((ForcingGuardCode.compiled false R w B f (v 1) (v 4)).conj ((ForcingExistGuardsCode.compiled R w A B f j (v 5)).conj ((ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder H) w C f (v 1) (v 6)).conj ((ForcingExistChildCode.compiled w a A B C f j N (v 7)).conj (shell w a A B C f (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) Q)))))))
private theorem data_rename {n m l} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m)
    (v : Fin 8 → Fin m) (r : Fin m → Fin l) :
    (data R H w a A B C f j N Q v).rename r = data R H (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) (r Q) (fun i => r (v i)) := by
  simp only [data, Formula.rename, SyntaxMixedImageHead.head_rename, ForcingGuardCode.compiled_rename,
    ForcingExistGuardsCode.compiled_rename, ForcingExistChildCode.compiled_rename, shell_rename]
private def body {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m) : Formula (m+8) :=
  data R H (old 8 w) (old 8 a) (old 8 A) (old 8 B) (old 8 C) (old 8 f) (old 8 j) (old 8 N) (old 8 Q) (slot 8)

/-- Literal ALL/EX/EX code, with all executions existentially bound internally.
Child N is at a+1, because its new-name binder has already been interpreted. -/
def compiled {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral (n+1) j).conj (existsMany 8 (body R H w a A B C f j N Q))
theorem compiled_rename {n m l} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m) (r : Fin m → Fin l) :
    (compiled R H w a A B C f j N Q).rename r = compiled R H (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) (r Q) := by
  simp only [compiled, Formula.rename, SyntaxNumeralSyntax.numeral_rename, existsMany_rename, body, data_rename, lift_old, lift_slot]
def existsCompiled {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N : Fin m) : Formula m := .ex
  (compiled R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m))
private theorem existsCompiled_rename {n m l} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N : Fin m) (r : Fin m → Fin l) :
    (existsCompiled R H w a A B C f j N).rename r = existsCompiled R H (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) := by
  simp only [existsCompiled, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private structure Inputs {m} (n : Nat) (Γ : Context m) (w a A B C f j N : Fin m) : Prop where
  hw : Derives Γ (omega w)
  ha : Derives Γ (Formula.mem a w)
  hA : Derives Γ (successor A a)
  hB : Derives Γ (successor B A)
  hC : Derives Γ (successor C B)
  hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)
  hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j)
  hn : Derives Γ (formulaCode w N A f)
private theorem underInputs {n m} {Γ : Context m} {w a A B C f j N : Fin m}
    (h : Inputs n Γ w a A B C f j N) (T : Formula (m+1)) :
    Inputs n (Context.add T (Context.image Formula.raise Γ)) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc := by
  exact ⟨of_eq (omega_rename w Fin.castSucc) (under h.hw T),
    (under h.ha T),
    of_eq (successor_rename A a Fin.castSucc) (under h.hA T),
    of_eq (successor_rename B A Fin.castSucc) (under h.hB T),
    of_eq (successor_rename C B Fin.castSucc) (under h.hC T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under h.hf T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+1) j Fin.castSucc) (under h.hj T),
    of_eq (formulaCode_rename w N A f Fin.castSucc) (under h.hn T)⟩

private theorem underInputs2 {n m} {Γ : Context m} {w a A B C f j N : Fin m}
    (h : Inputs n Γ w a A B C f j N) (T : Formula (m+2)) :
    Inputs n (Context.add T (raisedContext 2 Γ)) (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 f) (old 2 j) (old 2 N) := by
  exact ⟨of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 h.hw T),
    (HornBinderRules.under_body 2 h.ha T),
    of_eq (successor_rename A a (old 2)) (HornBinderRules.under_body 2 h.hA T),
    of_eq (successor_rename B A (old 2)) (HornBinderRules.under_body 2 h.hB T),
    of_eq (successor_rename C B (old 2)) (HornBinderRules.under_body 2 h.hC T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f (old 2)) (HornBinderRules.under_body 2 h.hf T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+1) j (old 2)) (HornBinderRules.under_body 2 h.hj T),
    of_eq (formulaCode_rename w N A f (old 2)) (HornBinderRules.under_body 2 h.hn T)⟩

private theorem scopeA {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {w a A B C f j N : Fin m}
    (h : Inputs n Γ w a A B C f j N) : Derives Γ (.mem A w) :=
  OmegaStructureAlgebra.successor_member w A a (ZFContext.arithmetic hZ).base.extensionality h.hw h.ha h.hA
private theorem scopeB {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {w a A B C f j N : Fin m}
    (h : Inputs n Γ w a A B C f j N) : Derives Γ (.mem B w) :=
  OmegaStructureAlgebra.successor_member w B A (ZFContext.arithmetic hZ).base.extensionality h.hw (scopeA hZ h) h.hB

private theorem inputs_stage7 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N z t qM qO rM rO D Nc : Fin m)
    (h : Inputs n Γ w a A B C f j N)
    (hh : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    (hm : Derives Γ (ForcingGuardCode.compiled false R w A f t qM))
    (ho : Derives Γ (ForcingGuardCode.compiled true R w A f t qO))
    (hr : Derives Γ (ForcingGuardCode.compiled false R w B f t rM))
    (hs : Derives Γ (ForcingExistGuardsCode.compiled R w A B f j rO))
    (hd : Derives Γ (ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder H) w C f t D))
    (hc : Derives Γ (ForcingExistChildCode.compiled w a A B C f j N Nc))
    : Derives Γ (existsCompiled R H w a A B C f j N) := by
  have hf := SyntaxNumerals.range hZ (n+2) w f h.hw h.hf
  have hAm := scopeA hZ h
  have hBm := scopeB hZ h
  have hCm := OmegaStructureAlgebra.successor_member w C B (ZFContext.arithmetic hZ).base.extensionality h.hw hBm h.hC
  have hi : ShellInputs Γ w a A B C f qM qO rM rO D Nc := ⟨h.hw,h.hA,h.hB,h.hC,
    .conjI h.ha hf,.conjI hAm hf,.conjI hBm hf,.conjI hCm hf,
    ForcingGuardCode.compiled_type false R w A f t qM hm,
    ForcingGuardCode.compiled_type true R w A f t qO ho,
    ForcingGuardCode.compiled_type false R w B f t rM hr,
    ForcingExistGuardsCode.compiled_type R w A B f j rO hs,
    ForcingGuardCode.compiled_type true (ForcingExistGuardsCode.domainOrder H) w C f t D hd,
    ForcingExistChildCode.compiled_type w a A B C f j N Nc hc⟩
  let T := shell w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc qM.castSucc qO.castSucc rM.castSucc rO.castSucc D.castSucc Nc.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (shell_stage0 hZ w a A B C f qM qO rM rO D Nc hi)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hhu := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under hh T)
  have hmu := of_eq (ForcingGuardCode.compiled_rename false R w A f t qM Fin.castSucc) (under hm T)
  have hou := of_eq (ForcingGuardCode.compiled_rename true R w A f t qO Fin.castSucc) (under ho T)
  have hru := of_eq (ForcingGuardCode.compiled_rename false R w B f t rM Fin.castSucc) (under hr T)
  have hsu := of_eq (ForcingExistGuardsCode.compiled_rename R w A B f j rO Fin.castSucc) (under hs T)
  have hdu := of_eq (ForcingGuardCode.compiled_rename true (ForcingExistGuardsCode.domainOrder H) w C f t D Fin.castSucc) (under hd T)
  have hcu := of_eq (ForcingExistChildCode.compiled_rename w a A B C f j N Nc Fin.castSucc) (under hc T)
  let v : Fin 8 → Fin (m+1) := Fin.cases z.castSucc (Fin.cases t.castSucc (Fin.cases qM.castSucc (Fin.cases qO.castSucc (Fin.cases rM.castSucc (Fin.cases rO.castSucc (Fin.cases D.castSucc (Fin.cases Nc.castSucc (fun i => Fin.elim0 i))))))))
  have ht : Derives Δ (data R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m) v) :=
    (.conjI hhu (.conjI hmu (.conjI hou (.conjI hru (.conjI hsu (.conjI hdu (.conjI hcu hT)))))))
  have hb : Derives Δ (existsMany 8 (body R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m))) := by
    apply HornBinderRules.intro_many 8 _ v
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]) ht
  have hj := of_eq (SyntaxNumeralSyntax.numeral_rename (n+1) j Fin.castSucc) (under h.hj T)
  have hq : Derives Δ (compiled R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)) := .conjI hj hb
  have ho : Derives Δ (existsCompiled R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq
  exact of_eq (existsCompiled_rename R H w a A B C f j N Fin.castSucc).symm ho

private theorem inputs_stage6 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N z t qM qO rM rO D : Fin m)
    (h : Inputs n Γ w a A B C f j N)
    (hh : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    (hm : Derives Γ (ForcingGuardCode.compiled false R w A f t qM))
    (ho : Derives Γ (ForcingGuardCode.compiled true R w A f t qO))
    (hr : Derives Γ (ForcingGuardCode.compiled false R w B f t rM))
    (hs : Derives Γ (ForcingExistGuardsCode.compiled R w A B f j rO))
    (hd : Derives Γ (ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder H) w C f t D))
    : Derives Γ (existsCompiled R H w a A B C f j N) := by
  let T := ForcingExistChildCode.compiled w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingExistChildCode.total hZ w a A B C f j N h.hw h.ha h.hA h.hB h.hC h.hn)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hhu := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under hh T)
  have hmu := of_eq (ForcingGuardCode.compiled_rename false R w A f t qM Fin.castSucc) (under hm T)
  have hou := of_eq (ForcingGuardCode.compiled_rename true R w A f t qO Fin.castSucc) (under ho T)
  have hru := of_eq (ForcingGuardCode.compiled_rename false R w B f t rM Fin.castSucc) (under hr T)
  have hsu := of_eq (ForcingExistGuardsCode.compiled_rename R w A B f j rO Fin.castSucc) (under hs T)
  have hdu := of_eq (ForcingGuardCode.compiled_rename true (ForcingExistGuardsCode.domainOrder H) w C f t D Fin.castSucc) (under hd T)
  have ho := inputs_stage7 (ZFContext.under hZ T) R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc z.castSucc t.castSucc qM.castSucc qO.castSucc rM.castSucc rO.castSucc D.castSucc (Fin.last m) (underInputs h T) hhu hmu hou hru hsu hdu hT
  exact of_eq (existsCompiled_rename R H w a A B C f j N Fin.castSucc).symm ho

private theorem inputs_stage5 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N z t qM qO rM rO : Fin m)
    (h : Inputs n Γ w a A B C f j N)
    (hh : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    (hm : Derives Γ (ForcingGuardCode.compiled false R w A f t qM))
    (ho : Derives Γ (ForcingGuardCode.compiled true R w A f t qO))
    (hr : Derives Γ (ForcingGuardCode.compiled false R w B f t rM))
    (hs : Derives Γ (ForcingExistGuardsCode.compiled R w A B f j rO))
    : Derives Γ (existsCompiled R H w a A B C f j N) := by
  let T := ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder H) w.castSucc C.castSucc f.castSucc t.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingGuardCode.total hZ true (ForcingExistGuardsCode.domainOrder H) w C f t h.hw h.hf (.conjR (.conjR hh)))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hhu := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under hh T)
  have hmu := of_eq (ForcingGuardCode.compiled_rename false R w A f t qM Fin.castSucc) (under hm T)
  have hou := of_eq (ForcingGuardCode.compiled_rename true R w A f t qO Fin.castSucc) (under ho T)
  have hru := of_eq (ForcingGuardCode.compiled_rename false R w B f t rM Fin.castSucc) (under hr T)
  have hsu := of_eq (ForcingExistGuardsCode.compiled_rename R w A B f j rO Fin.castSucc) (under hs T)
  have ho := inputs_stage6 (ZFContext.under hZ T) R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc z.castSucc t.castSucc qM.castSucc qO.castSucc rM.castSucc rO.castSucc (Fin.last m) (underInputs h T) hhu hmu hou hru hsu hT
  exact of_eq (existsCompiled_rename R H w a A B C f j N Fin.castSucc).symm ho

private theorem inputs_stage4 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N z t qM qO rM : Fin m)
    (h : Inputs n Γ w a A B C f j N)
    (hh : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    (hm : Derives Γ (ForcingGuardCode.compiled false R w A f t qM))
    (ho : Derives Γ (ForcingGuardCode.compiled true R w A f t qO))
    (hr : Derives Γ (ForcingGuardCode.compiled false R w B f t rM))
    : Derives Γ (existsCompiled R H w a A B C f j N) := by
  let T := ForcingExistGuardsCode.compiled R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingExistGuardsCode.total hZ R w a A B f j h.hw h.ha h.hA h.hB h.hf h.hj)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hhu := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under hh T)
  have hmu := of_eq (ForcingGuardCode.compiled_rename false R w A f t qM Fin.castSucc) (under hm T)
  have hou := of_eq (ForcingGuardCode.compiled_rename true R w A f t qO Fin.castSucc) (under ho T)
  have hru := of_eq (ForcingGuardCode.compiled_rename false R w B f t rM Fin.castSucc) (under hr T)
  have ho := inputs_stage5 (ZFContext.under hZ T) R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc z.castSucc t.castSucc qM.castSucc qO.castSucc rM.castSucc (Fin.last m) (underInputs h T) hhu hmu hou hru hT
  exact of_eq (existsCompiled_rename R H w a A B C f j N Fin.castSucc).symm ho

private theorem inputs_stage3 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N z t qM qO : Fin m)
    (h : Inputs n Γ w a A B C f j N)
    (hh : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    (hm : Derives Γ (ForcingGuardCode.compiled false R w A f t qM))
    (ho : Derives Γ (ForcingGuardCode.compiled true R w A f t qO))
    : Derives Γ (existsCompiled R H w a A B C f j N) := by
  have ht := SyntaxMixedImageHead.term_at_zero hZ w A B f z t h.hw (scopeA hZ h)
    (SyntaxNumerals.range hZ (n+2) w f h.hw h.hf) h.hB (.conjL hh) (.conjL (.conjR hh))
  let T := ForcingGuardCode.compiled false R w.castSucc B.castSucc f.castSucc t.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingGuardCode.total hZ false R w B f t h.hw h.hf ht)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hhu := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under hh T)
  have hmu := of_eq (ForcingGuardCode.compiled_rename false R w A f t qM Fin.castSucc) (under hm T)
  have hou := of_eq (ForcingGuardCode.compiled_rename true R w A f t qO Fin.castSucc) (under ho T)
  have ho := inputs_stage4 (ZFContext.under hZ T) R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc z.castSucc t.castSucc qM.castSucc qO.castSucc (Fin.last m) (underInputs h T) hhu hmu hou hT
  exact of_eq (existsCompiled_rename R H w a A B C f j N Fin.castSucc).symm ho

private theorem inputs_stage2 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N z t qM : Fin m)
    (h : Inputs n Γ w a A B C f j N)
    (hh : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    (hm : Derives Γ (ForcingGuardCode.compiled false R w A f t qM))
    : Derives Γ (existsCompiled R H w a A B C f j N) := by
  have ht := SyntaxMixedImageHead.term_at_zero hZ w a A f z t h.hw h.ha
    (SyntaxNumerals.range hZ (n+2) w f h.hw h.hf) h.hA (.conjL hh) (.conjL (.conjR hh))
  let T := ForcingGuardCode.compiled true R w.castSucc A.castSucc f.castSucc t.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingGuardCode.total hZ true R w A f t h.hw h.hf ht)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hhu := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under hh T)
  have hmu := of_eq (ForcingGuardCode.compiled_rename false R w A f t qM Fin.castSucc) (under hm T)
  have ho := inputs_stage3 (ZFContext.under hZ T) R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc z.castSucc t.castSucc qM.castSucc (Fin.last m) (underInputs h T) hhu hmu hT
  exact of_eq (existsCompiled_rename R H w a A B C f j N Fin.castSucc).symm ho

private theorem inputs_stage1 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N z t : Fin m)
    (h : Inputs n Γ w a A B C f j N)
    (hh : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    : Derives Γ (existsCompiled R H w a A B C f j N) := by
  have ht := SyntaxMixedImageHead.term_at_zero hZ w a A f z t h.hw h.ha
    (SyntaxNumerals.range hZ (n+2) w f h.hw h.hf) h.hA (.conjL hh) (.conjL (.conjR hh))
  let T := ForcingGuardCode.compiled false R w.castSucc A.castSucc f.castSucc t.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingGuardCode.total hZ false R w A f t h.hw h.hf ht)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hhu := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under hh T)
  have ho := inputs_stage2 (ZFContext.under hZ T) R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc z.castSucc t.castSucc (Fin.last m) (underInputs h T) hhu hT
  exact of_eq (existsCompiled_rename R H w a A B C f j N Fin.castSucc).symm ho

/-- An arbitrary internally valid child, with no supplied compiler output. -/
theorem total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j))
    (hn : Derives Γ (formulaCode w N A f)) : Derives Γ (existsCompiled R H w a A B C f j N) := by
  have h : Inputs n Γ w a A B C f j N := ⟨hw,ha,hA,hB,hC,hf,hj,hn⟩
  let T := SyntaxMixedImageHead.head (old 2 w) (old 2 C) (old 2 f) (slot 2 0) (slot 2 1)
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ (SyntaxMixedImageHead.exists_head hZ w B C f hw (scopeB hZ h)
    (SyntaxNumerals.range hZ (n+2) w f hw hf) hC)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ho := inputs_stage1 (HornBinderRules.zf_body 2 hZ T) R H (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 f) (old 2 j) (old 2 N)
    (slot 2 0) (slot 2 1) (underInputs2 h T) hT
  exact of_eq (existsCompiled_rename R H w a A B C f j N (old 2)).symm ho

theorem compiled_type {n m} {Γ : Context m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m)
    (h : Derives Γ (compiled R H w a A B C f j N Q)) : Derives Γ (formulaCode w Q a f) := by
  let T := body R H w a A B C f j N Q
  let Δ := Context.add T (raisedContext 8 Γ)
  apply HornBinderRules.eliminate_many 8 T _ (.conjR h)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w Q a f (old 8)).symm
    (shell_type (old 8 w) (old 8 a) (old 8 A) (old 8 B) (old 8 C) (old 8 f) (slot 8 2) (slot 8 3) (slot 8 4) (slot 8 5) (slot 8 6) (slot 8 7) (old 8 Q) (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hT))))))))

private theorem guard_input_subst {n m} {Γ : Context m} (order : Bool) (R : Source.Formula (n+2))
    (w b f x Q y : Fin m) (he : Derives Γ (.equal x y))
    (h : Derives Γ (ForcingGuardCode.compiled order R w b f x Q)) : Derives Γ (ForcingGuardCode.compiled order R w b f y Q) := by
  let P := ForcingGuardCode.compiled order R w.castSucc b.castSucc f.castSucc (Fin.last m) Q.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, ForcingGuardCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, ForcingGuardCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))

private theorem shell_inputs_subst {m} {Γ : Context m} (w a A B C f qM qO rM rO D Nc Q uM uO vM vO E K : Fin m)
    (e0 : Derives Γ (.equal qM uM))
    (e1 : Derives Γ (.equal qO uO))
    (e2 : Derives Γ (.equal rM vM))
    (e3 : Derives Γ (.equal rO vO))
    (e4 : Derives Γ (.equal D E))
    (e5 : Derives Γ (.equal Nc K))
    (h : Derives Γ (shell w a A B C f qM qO rM rO D Nc Q)) : Derives Γ (shell w a A B C f uM uO vM vO E K Q) := by
  let P0 := shell w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc (Fin.last m) qO.castSucc rM.castSucc rO.castSucc D.castSucc Nc.castSucc Q.castSucc
  have h0 : Derives Γ (shell w a A B C f uM qO rM rO D Nc Q) :=
    of_eq (by simp only [P0, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P0 e0 (of_eq (by simp only [P0, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  let P1 := shell w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc uM.castSucc (Fin.last m) rM.castSucc rO.castSucc D.castSucc Nc.castSucc Q.castSucc
  have h1 : Derives Γ (shell w a A B C f uM uO rM rO D Nc Q) :=
    of_eq (by simp only [P1, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P1 e1 (of_eq (by simp only [P1, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h0))
  let P2 := shell w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc uM.castSucc uO.castSucc (Fin.last m) rO.castSucc D.castSucc Nc.castSucc Q.castSucc
  have h2 : Derives Γ (shell w a A B C f uM uO vM rO D Nc Q) :=
    of_eq (by simp only [P2, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P2 e2 (of_eq (by simp only [P2, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h1))
  let P3 := shell w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc uM.castSucc uO.castSucc vM.castSucc (Fin.last m) D.castSucc Nc.castSucc Q.castSucc
  have h3 : Derives Γ (shell w a A B C f uM uO vM vO D Nc Q) :=
    of_eq (by simp only [P3, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P3 e3 (of_eq (by simp only [P3, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h2))
  let P4 := shell w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc uM.castSucc uO.castSucc vM.castSucc vO.castSucc (Fin.last m) Nc.castSucc Q.castSucc
  have h4 : Derives Γ (shell w a A B C f uM uO vM vO E Nc Q) :=
    of_eq (by simp only [P4, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P4 e4 (of_eq (by simp only [P4, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h3))
  let P5 := shell w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc uM.castSucc uO.castSucc vM.castSucc vO.castSucc E.castSucc (Fin.last m) Q.castSucc
  have h5 : Derives Γ (shell w a A B C f uM uO vM vO E K Q) :=
    of_eq (by simp only [P5, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P5 e5 (of_eq (by simp only [P5, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h4))
  exact h5

private theorem data_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q V : Fin m)
    (xs ys : Fin 8 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (data R H w a A B C f j N Q xs)) (hy : Derives Γ (data R H w a A B C f j N V ys)) : Derives Γ (.equal Q V) := by
  have hhx := Derives.conjL hx
  have hhy := Derives.conjL hy
  have hz := OmegaUniversal.empty_unique (xs 0) (ys 0) (ZFContext.arithmetic hZ).base.extensionality (.conjL hhx) (.conjL hhy)
  have hcode := AbstractVariableIndex.code_index_subst true w (xs 0) (ys 0) (xs 1) hz (.conjL (.conjR hhx))
  have ht := SyntaxVariables.unique hZ true w (ys 0) (xs 1) (ys 1) hw hcode (.conjL (.conjR hhy))
  have g1 := guard_input_subst false R w A f (xs 1) (xs 2) (ys 1) ht (.conjL (.conjR hx))
  have e1 := ForcingGuardCode.unique hZ false R w A f (ys 1) (xs 2) (ys 2) hw g1 (.conjL (.conjR hy))
  have g2 := guard_input_subst true R w A f (xs 1) (xs 3) (ys 1) ht (.conjL (.conjR (.conjR hx)))
  have e2 := ForcingGuardCode.unique hZ true R w A f (ys 1) (xs 3) (ys 3) hw g2 (.conjL (.conjR (.conjR hy)))
  have g3 := guard_input_subst false R w B f (xs 1) (xs 4) (ys 1) ht (.conjL (.conjR (.conjR (.conjR hx))))
  have e3 := ForcingGuardCode.unique hZ false R w B f (ys 1) (xs 4) (ys 4) hw g3 (.conjL (.conjR (.conjR (.conjR hy))))
  have g5 := guard_input_subst true (ForcingExistGuardsCode.domainOrder H) w C f (xs 1) (xs 6) (ys 1) ht (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hx))))))
  have e5 := ForcingGuardCode.unique hZ true (ForcingExistGuardsCode.domainOrder H) w C f (ys 1) (xs 6) (ys 6) hw g5 (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hy))))))
  have e4 := ForcingExistGuardsCode.unique hZ R w A B f j (xs 5) (ys 5) hw (.conjL (.conjR (.conjR (.conjR (.conjR hx))))) (.conjL (.conjR (.conjR (.conjR (.conjR hy)))))
  have e6 := ForcingExistChildCode.unique hZ w a A B C f j N (xs 7) (ys 7) hw (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hx))))))) (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hy)))))))
  have hs := shell_inputs_subst w a A B C f (xs 2) (xs 3) (xs 4) (xs 5) (xs 6) (xs 7) Q (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) e1 e2 e3 e4 e5 e6 (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hx)))))))
  exact shell_unique hZ w a A B C f (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) Q V hw hs (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hy)))))))

/-- Two independently executed branches have the same output. -/
theorem unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q V : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled R H w a A B C f j N Q)) (hv : Derives Γ (compiled R H w a A B C f j N V)) : Derives Γ (.equal Q V) := by
  let T := body R H w a A B C f j N Q
  let Δ := Context.add T (raisedContext 8 Γ)
  apply HornBinderRules.eliminate_many 8 T _ (.conjR hq)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hv1 := of_eq (compiled_rename R H w a A B C f j N V (old 8)) (HornBinderRules.under_body 8 hv T)
  let U := body R H (old 8 w) (old 8 a) (old 8 A) (old 8 B) (old 8 C) (old 8 f) (old 8 j) (old 8 N) (old 8 V)
  let Ξ := Context.add U (raisedContext 8 Δ)
  apply HornBinderRules.eliminate_many 8 U _ (.conjR hv1)
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hw2 : Derives Ξ (omega (old 8 (old 8 w))) := of_eq (by simp only [omega_rename])
    (HornBinderRules.under_body 8 (HornBinderRules.under_body 8 hw T) U)
  have hx2 : Derives Ξ (data R H (old 8 (old 8 w)) (old 8 (old 8 a)) (old 8 (old 8 A)) (old 8 (old 8 B)) (old 8 (old 8 C)) (old 8 (old 8 f)) (old 8 (old 8 j)) (old 8 (old 8 N)) (old 8 (old 8 Q)) (fun i => old 8 (slot 8 i))) :=
    of_eq (by simp only [T, body, data_rename]) (HornBinderRules.under_body 8 hT U)
  exact data_unique (HornBinderRules.zf_body 8 (HornBinderRules.zf_body 8 hZ T) U) R H
    (old 8 (old 8 w)) (old 8 (old 8 a)) (old 8 (old 8 A)) (old 8 (old 8 B)) (old 8 (old 8 C)) (old 8 (old 8 f)) (old 8 (old 8 j)) (old 8 (old 8 N)) (old 8 (old 8 Q)) (old 8 (old 8 V))
    (fun i => old 8 (slot 8 i)) (slot 8) hw2 hx2 hU

def uniqueOutput {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m) : Formula m := .all
  ((compiled R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)).imp (.equal (Fin.last m) Q.castSucc))
private theorem uniqueOutput_rename {n m l} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m) (r : Fin m → Fin l) :
    (uniqueOutput R H w a A B C f j N Q).rename r = uniqueOutput R H (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) (r Q) := by
  simp only [uniqueOutput, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
private theorem unique_output {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2)) (H : Source.Formula (n+1))
    (w a A B C f j N Q : Fin m) (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled R H w a A B C f j N Q)) :
    Derives Γ (uniqueOutput R H w a A B C f j N Q) := by
  apply Derives.allI
  apply Derives.impI
  let T := compiled R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)
  exact unique (ZFContext.under hZ T) R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m) Q.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (.hyp (Or.inl rfl))
    (of_eq (compiled_rename R H w a A B C f j N Q Fin.castSucc) (under hq T))

def fiber {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N : Fin m) : Formula m := .ex
  ((compiled R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)).conj
    ((formulaCode w.castSucc (Fin.last m) a.castSucc f.castSucc).conj
      (uniqueOutput R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m))))
private theorem fiber_rename {n m l} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N : Fin m) (r : Fin m → Fin l) :
    (fiber R H w a A B C f j N).rename r = fiber R H (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) := by
  simp only [fiber, Formula.rename, compiled_rename, formulaCode_rename, uniqueOutput_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2)) (H : Source.Formula (n+1))
    (w a A B C f j N : Fin m) (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j))
    (hN : Derives Γ (formulaCode w N A f)) : Derives Γ (fiber R H w a A B C f j N) := by
  let T := compiled R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (total hZ R H w a A B C f j N hw ha hA hB hC hf hj hN)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ht := compiled_type R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m) hT
  have hu := unique_output (ZFContext.under hZ T) R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) hT
  have ho : Derives Δ (fiber R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [T, Formula.instantiate, Formula.rename, compiled_rename, formulaCode_rename,
      uniqueOutput_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hT (.conjI ht hu))
  exact of_eq (fiber_rename R H w a A B C f j N Fin.castSucc).symm ho


def sentence {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N : Fin m) : Source.Sentence :=
  ((omega w).imp ((Formula.mem a w).imp ((successor A a).imp ((successor B A).imp ((successor C B).imp ((SyntaxNumeralSyntax.numeral (n+2) f).imp ((SyntaxNumeralSyntax.numeral (n+1) j).imp ((formulaCode w N A f).imp (fiber R H w a A B C f j N))))))))).close
theorem kernel_certificate {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R H w a A B C f j N)) := by
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
  exact fiber_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) _) _) _) R H w a A B C f j N
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
def uniqueSentence {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q V : Fin m) : Source.Sentence :=
  ((omega w).imp ((compiled R H w a A B C f j N Q).imp ((compiled R H w a A B C f j N V).imp (.equal Q V)))).close
theorem unique_kernel_certificate {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q V : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (uniqueSentence R H w a A B C f j N Q V)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact unique (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) R H w a A B C f j N Q V (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingExistCode
