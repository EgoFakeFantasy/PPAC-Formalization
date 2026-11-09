import PPAC.Migration.ForcingGuardCode
import PPAC.Migration.Internal.FormulaCodeConstructors

/-! The literal original negative branch: ALL q in P, R(q,p) ->
(child[p:=q] -> falsum). Existing native constructors and mixed rebind are
used. This is one recursion step, not a full interpreter or a Con proof. -/
namespace PPAC.Migration.ForcingNegCode
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeConstructSyntax (typedAt typedAt_rename typedExists)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
set_option maxRecDepth 16384

private def botAt {m} (w A f B : Fin m) : Formula m := typedAt 0 0 w Fin.elim0 B A f
private def impAt {m} (w A f x y Q : Fin m) : Formula m := typedAt 2 7 w (SyntaxAtomSyntax.two x y) Q A f
private def allAt {m} (w a f J Q : Fin m) : Formula m := typedAt 1 9 w (fun _ => J) Q a f

private theorem botAt_rename {m l} (w A f B : Fin m) (r : Fin m → Fin l) :
    (botAt w A f B).rename r = botAt (r w) (r A) (r f) (r B) := by
  simp only [botAt, typedAt_rename, SyntaxAtomSyntax.zero_map]
private theorem impAt_rename {m l} (w A f x y Q : Fin m) (r : Fin m → Fin l) :
    (impAt w A f x y Q).rename r = impAt (r w) (r A) (r f) (r x) (r y) (r Q) := by
  simp only [impAt, typedAt_rename, SyntaxAtomSyntax.two_map]
private theorem allAt_rename {m l} (w a f J Q : Fin m) (r : Fin m → Fin l) :
    (allAt w a f J Q).rename r = allAt (r w) (r a) (r f) (r J) (r Q) := by
  simp only [allAt, typedAt_rename]

def shellData {m} (w a A f M O C Q : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (botAt w A f (v 0)).conj ((impAt w A f C (v 0) (v 1)).conj
    ((impAt w A f O (v 1) (v 2)).conj ((impAt w A f M (v 2) (v 3)).conj
      (allAt w a f (v 3) Q))))
theorem shellData_rename {m l} (w a A f M O C Q : Fin m) (v : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (shellData w a A f M O C Q v).rename r = shellData (r w) (r a) (r A) (r f) (r M) (r O) (r C) (r Q) (fun i => r (v i)) := by
  simp only [shellData, Formula.rename, botAt_rename, impAt_rename, allAt_rename]
def shellBody {m} (w a A f M O C Q : Fin m) : Formula (m+4) :=
  shellData (old 4 w) (old 4 a) (old 4 A) (old 4 f) (old 4 M) (old 4 O) (old 4 C) (old 4 Q) (slot 4)
private def shell {m} (w a A f M O C Q : Fin m) : Formula m := existsMany 4 (shellBody w a A f M O C Q)
private theorem shell_rename {m l} (w a A f M O C Q : Fin m) (r : Fin m → Fin l) :
    (shell w a A f M O C Q).rename r = shell (r w) (r a) (r A) (r f) (r M) (r O) (r C) (r Q) := by
  simp only [shell, existsMany_rename, shellBody, shellData_rename, lift_old, lift_slot]
private def existsShell {m} (w a A f M O C : Fin m) : Formula m := .ex
  (shell w.castSucc a.castSucc A.castSucc f.castSucc M.castSucc O.castSucc C.castSucc (Fin.last m))
private theorem existsShell_rename {m l} (w a A f M O C : Fin m) (r : Fin m → Fin l) :
    (existsShell w a A f M O C).rename r = existsShell (r w) (r a) (r A) (r f) (r M) (r O) (r C) := by
  simp only [existsShell, Formula.rename, shell_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private structure ShellInputs {m} (Γ : Context m) (w a A f M O C : Fin m) : Prop where
  hw : Derives Γ (omega w)
  hs : Derives Γ (successor A a)
  ha : Derives Γ (SyntaxTermSyntax.contexts w a f)
  hm : Derives Γ (formulaCode w M A f)
  ho : Derives Γ (formulaCode w O A f)
  hc : Derives Γ (formulaCode w C A f)
private theorem underShell {m} {Γ : Context m} {w a A f M O C : Fin m}
    (h : ShellInputs Γ w a A f M O C) (B : Formula (m+1)) :
    ShellInputs (Context.add B (Context.image Formula.raise Γ)) w.castSucc a.castSucc A.castSucc f.castSucc M.castSucc O.castSucc C.castSucc := by
  exact ⟨of_eq (omega_rename w Fin.castSucc) (under h.hw B),
    of_eq (successor_rename A a Fin.castSucc) (under h.hs B),
    of_eq (SyntaxTermSyntax.contexts_rename w a f Fin.castSucc) (under h.ha B),
    of_eq (formulaCode_rename w M A f Fin.castSucc) (under h.hm B),
    of_eq (formulaCode_rename w O A f Fin.castSucc) (under h.ho B),
    of_eq (formulaCode_rename w C A f Fin.castSucc) (under h.hc B)⟩

private theorem shell_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A f M O C B N I J : Fin m) (h : ShellInputs Γ w a A f M O C)
    (hB : Derives Γ (botAt w A f B)) (hN : Derives Γ (impAt w A f C B N))
    (hI : Derives Γ (impAt w A f O N I)) (hJ : Derives Γ (impAt w A f M I J)) :
    Derives Γ (existsShell w a A f M O C) := by
  have ht : Derives Γ (FormulaCodeBranchSyntax.singleTypes true w a f J) := .conjI h.ha
    (FormulaCodeRecursiveSyntax.intro_advanced w J a f A h.hs (.conjR hJ))
  have he := FormulaCodeConstruct.exists_of_fiber 1 9 w (fun _ => J) a f (FormulaCodeConstructors.universal hZ w a f J h.hw ht)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (allAt w.castSucc a.castSucc f.castSucc J.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hb := of_eq (botAt_rename w A f B Fin.castSucc) (under hB T)
  have hn := of_eq (impAt_rename w A f C B N Fin.castSucc) (under hN T)
  have hi := of_eq (impAt_rename w A f O N I Fin.castSucc) (under hI T)
  have hj := of_eq (impAt_rename w A f M I J Fin.castSucc) (under hJ T)
  let v : Fin 4 → Fin (m+1) := Fin.cases B.castSucc (Fin.cases N.castSucc (SetLanguage.args2 I.castSucc J.castSucc))
  have hd : Derives Δ (shellData w.castSucc a.castSucc A.castSucc f.castSucc M.castSucc O.castSucc C.castSucc (Fin.last m) v) :=
    .conjI hb (.conjI hn (.conjI hi (.conjI hj (.conjR hT))))
  have hc : Derives Δ (shell w.castSucc a.castSucc A.castSucc f.castSucc M.castSucc O.castSucc C.castSucc (Fin.last m)) := by
    apply HornBinderRules.intro_many 4 _ v
    exact of_eq (by simp only [shellBody, shellData_rename, assign_old, assign_slot]) hd
  have ho : Derives Δ (existsShell w.castSucc a.castSucc A.castSucc f.castSucc M.castSucc O.castSucc C.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (existsShell_rename w a A f M O C Fin.castSucc).symm ho

private theorem shell_stage3 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A f M O C B N I: Fin m) (h : ShellInputs Γ w a A f M O C)
    (hB : Derives Γ (botAt w A f B))
    (hN : Derives Γ (impAt w A f C B N))
    (hI : Derives Γ (impAt w A f O N I))
    : Derives Γ (existsShell w a A f M O C) := by
  have he := FormulaCodeConstruct.exists_of_fiber 2 7 w (SyntaxAtomSyntax.two M I) A f
    (FormulaCodeConstructors.binary2 hZ w A f M I h.hw
      (.conjI (.conjR (FormulaCodeProperties.guards w M A f h.hm)) (.conjI (h.hm) (.conjR hI))))
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (impAt w.castSucc A.castSucc f.castSucc M.castSucc I.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hB1 := of_eq (botAt_rename w A f B Fin.castSucc) (under hB T)
  have hN1 := of_eq (impAt_rename w A f C B N Fin.castSucc) (under hN T)
  have hI1 := of_eq (impAt_rename w A f O N I Fin.castSucc) (under hI T)
  have ho := shell_complete (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc f.castSucc M.castSucc O.castSucc C.castSucc B.castSucc N.castSucc I.castSucc (Fin.last m) (underShell h T) hB1 hN1 hI1 (.conjR hT)
  exact of_eq (existsShell_rename w a A f M O C Fin.castSucc).symm ho

private theorem shell_stage2 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A f M O C B N: Fin m) (h : ShellInputs Γ w a A f M O C)
    (hB : Derives Γ (botAt w A f B))
    (hN : Derives Γ (impAt w A f C B N))
    : Derives Γ (existsShell w a A f M O C) := by
  have he := FormulaCodeConstruct.exists_of_fiber 2 7 w (SyntaxAtomSyntax.two O N) A f
    (FormulaCodeConstructors.binary2 hZ w A f O N h.hw
      (.conjI (.conjR (FormulaCodeProperties.guards w M A f h.hm)) (.conjI (h.ho) (.conjR hN))))
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (impAt w.castSucc A.castSucc f.castSucc O.castSucc N.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hB1 := of_eq (botAt_rename w A f B Fin.castSucc) (under hB T)
  have hN1 := of_eq (impAt_rename w A f C B N Fin.castSucc) (under hN T)
  have ho := shell_stage3 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc f.castSucc M.castSucc O.castSucc C.castSucc B.castSucc N.castSucc (Fin.last m) (underShell h T) hB1 hN1 (.conjR hT)
  exact of_eq (existsShell_rename w a A f M O C Fin.castSucc).symm ho

private theorem shell_stage1 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A f M O C B: Fin m) (h : ShellInputs Γ w a A f M O C)
    (hB : Derives Γ (botAt w A f B))
    : Derives Γ (existsShell w a A f M O C) := by
  have he := FormulaCodeConstruct.exists_of_fiber 2 7 w (SyntaxAtomSyntax.two C B) A f
    (FormulaCodeConstructors.binary2 hZ w A f C B h.hw
      (.conjI (.conjR (FormulaCodeProperties.guards w M A f h.hm)) (.conjI (h.hc) (.conjR hB))))
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (impAt w.castSucc A.castSucc f.castSucc C.castSucc B.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hB1 := of_eq (botAt_rename w A f B Fin.castSucc) (under hB T)
  have ho := shell_stage2 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc f.castSucc M.castSucc O.castSucc C.castSucc B.castSucc (Fin.last m) (underShell h T) hB1 (.conjR hT)
  exact of_eq (existsShell_rename w a A f M O C Fin.castSucc).symm ho

private theorem shell_stage0 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A f M O C: Fin m) (h : ShellInputs Γ w a A f M O C)
    : Derives Γ (existsShell w a A f M O C) := by
  have he := FormulaCodeConstruct.exists_of_fiber 0 0 w Fin.elim0 A f
    (FormulaCodeConstructors.nullary hZ false w A f h.hw (.conjR (FormulaCodeProperties.guards w M A f h.hm)))
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (botAt w.castSucc A.castSucc f.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ho := shell_stage1 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc f.castSucc M.castSucc O.castSucc C.castSucc (Fin.last m) (underShell h T)  (.conjR hT)
  exact of_eq (existsShell_rename w a A f M O C Fin.castSucc).symm ho


private theorem shell_type {m} {Γ : Context m} (w a A f M O C Q : Fin m)
    (h : Derives Γ (shell w a A f M O C Q)) : Derives Γ (formulaCode w Q a f) := by
  let B := shellBody w a A f M O C Q
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ h
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w Q a f (old 4)).symm (.conjR (.conjR (.conjR (.conjR (.conjR hB)))))

private theorem imp_right_subst {m} {Γ : Context m} (w A f x y Q Y : Fin m)
    (he : Derives Γ (.equal y Y)) (h : Derives Γ (impAt w A f x y Q)) : Derives Γ (impAt w A f x Y Q) := by
  let P := impAt w.castSucc A.castSucc f.castSucc x.castSucc (Fin.last m) Q.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, impAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, impAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
private theorem all_child_subst {m} {Γ : Context m} (w a f J Q K : Fin m)
    (he : Derives Γ (.equal J K)) (h : Derives Γ (allAt w a f J Q)) : Derives Γ (allAt w a f K Q) := by
  let P := allAt w.castSucc a.castSucc f.castSucc (Fin.last m) Q.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, allAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, allAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))

private theorem shellData_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A f M O C Q V : Fin m) (xs ys : Fin 4 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (shellData w a A f M O C Q xs)) (hy : Derives Γ (shellData w a A f M O C V ys)) :
    Derives Γ (.equal Q V) := by
  have hb := SyntaxConstructors.unique hZ 0 0 w Fin.elim0 (xs 0) (ys 0) hw (.conjL (.conjL hx)) (.conjL (.conjL hy))
  have hn := imp_right_subst w A f C (xs 0) (xs 1) (ys 0) hb (.conjL (.conjR hx))
  have hN := SyntaxConstructors.unique hZ 2 7 w (SyntaxAtomSyntax.two C (ys 0)) (xs 1) (ys 1) hw (.conjL hn) (.conjL (.conjL (.conjR hy)))
  have hi := imp_right_subst w A f O (xs 1) (xs 2) (ys 1) hN (.conjL (.conjR (.conjR hx)))
  have hI := SyntaxConstructors.unique hZ 2 7 w (SyntaxAtomSyntax.two O (ys 1)) (xs 2) (ys 2) hw (.conjL hi) (.conjL (.conjL (.conjR (.conjR hy))))
  have hj := imp_right_subst w A f M (xs 2) (xs 3) (ys 2) hI (.conjL (.conjR (.conjR (.conjR hx))))
  have hJ := SyntaxConstructors.unique hZ 2 7 w (SyntaxAtomSyntax.two M (ys 2)) (xs 3) (ys 3) hw (.conjL hj) (.conjL (.conjL (.conjR (.conjR (.conjR hy)))))
  have hq := all_child_subst w a f (xs 3) Q (ys 3) hJ (.conjR (.conjR (.conjR (.conjR hx))))
  exact SyntaxConstructors.unique hZ 1 9 w (fun _ => ys 3) Q V hw (.conjL hq) (.conjL (.conjR (.conjR (.conjR (.conjR hy)))))

private theorem shell_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A f M O C Q V : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (shell w a A f M O C Q)) (hv : Derives Γ (shell w a A f M O C V)) : Derives Γ (.equal Q V) := by
  let B := shellBody w a A f M O C Q
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ hq
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hv1 := of_eq (shell_rename w a A f M O C V (old 4)) (HornBinderRules.under_body 4 hv B)
  let T := shellBody (old 4 w) (old 4 a) (old 4 A) (old 4 f) (old 4 M) (old 4 O) (old 4 C) (old 4 V)
  let Ξ := Context.add T (raisedContext 4 Δ)
  apply HornBinderRules.eliminate_many 4 T _ hv1
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hw2 : Derives Ξ (omega (old 4 (old 4 w))) := of_eq (by simp only [omega_rename])
    (HornBinderRules.under_body 4 (HornBinderRules.under_body 4 hw B) T)
  have hx2 : Derives Ξ (shellData (old 4 (old 4 w)) (old 4 (old 4 a)) (old 4 (old 4 A)) (old 4 (old 4 f))
      (old 4 (old 4 M)) (old 4 (old 4 O)) (old 4 (old 4 C)) (old 4 (old 4 Q)) (fun i => old 4 (slot 4 i))) :=
    of_eq (by simp only [B, shellBody, shellData_rename]) (HornBinderRules.under_body 4 hB T)
  exact shellData_unique (HornBinderRules.zf_body 4 (HornBinderRules.zf_body 4 hZ B) T)
    (old 4 (old 4 w)) (old 4 (old 4 a)) (old 4 (old 4 A)) (old 4 (old 4 f))
    (old 4 (old 4 M)) (old 4 (old 4 O)) (old 4 (old 4 C)) (old 4 (old 4 Q)) (old 4 (old 4 V))
    (fun i => old 4 (slot 4 i)) (slot 4) hw2 hx2 hT

def data {n m} (R : Source.Formula (n+2)) (w a A f j N Q : Fin m) (v : Fin 5 → Fin m) : Formula m :=
  (SyntaxMixedImageHead.head w A f (v 0) (v 1)).conj
    ((ForcingConditionRebind.compiled w a f A j N (v 2)).conj
      ((ForcingGuardCode.compiled false R w A f (v 1) (v 3)).conj
        ((ForcingGuardCode.compiled true R w A f (v 1) (v 4)).conj
          (shell w a A f (v 3) (v 4) (v 2) Q))))
theorem data_rename {n m l} (R : Source.Formula (n+2)) (w a A f j N Q : Fin m)
    (v : Fin 5 → Fin m) (r : Fin m → Fin l) :
    (data R w a A f j N Q v).rename r = data R (r w) (r a) (r A) (r f) (r j) (r N) (r Q) (fun i => r (v i)) := by
  simp only [data, Formula.rename, SyntaxMixedImageHead.head_rename, ForcingConditionRebind.compiled_rename,
    ForcingGuardCode.compiled_rename, shell_rename]
def body {n m} (R : Source.Formula (n+2)) (w a A f j N Q : Fin m) : Formula (m+5) :=
  data R (old 5 w) (old 5 a) (old 5 A) (old 5 f) (old 5 j) (old 5 N) (old 5 Q) (slot 5)

/-- Actual child rebinding, both literal guards, and the whole ALL/IMP/BOT code
are inside object EX. j is exactly the original free condition slot n+1. -/
def compiled {n m} (R : Source.Formula (n+2)) (w a A f j N Q : Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral (n+1) j).conj (existsMany 5 (body R w a A f j N Q))
theorem compiled_rename {n m l} (R : Source.Formula (n+2)) (w a A f j N Q : Fin m) (r : Fin m → Fin l) :
    (compiled R w a A f j N Q).rename r = compiled R (r w) (r a) (r A) (r f) (r j) (r N) (r Q) := by
  simp only [compiled, Formula.rename, SyntaxNumeralSyntax.numeral_rename, existsMany_rename, body, data_rename, lift_old, lift_slot]
def existsCompiled {n m} (R : Source.Formula (n+2)) (w a A f j N : Fin m) : Formula m := .ex
  (compiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m))
private theorem existsCompiled_rename {n m l} (R : Source.Formula (n+2)) (w a A f j N : Fin m) (r : Fin m → Fin l) :
    (existsCompiled R w a A f j N).rename r = existsCompiled R (r w) (r a) (r A) (r f) (r j) (r N) := by
  simp only [existsCompiled, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private structure Inputs {m} (n : Nat) (Γ : Context m) (w a A f j N : Fin m) : Prop where
  hw : Derives Γ (omega w)
  hs : Derives Γ (successor A a)
  hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)
  hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j)
  hn : Derives Γ (formulaCode w N a f)
private theorem underInputs {n m} {Γ : Context m} {w a A f j N : Fin m}
    (h : Inputs n Γ w a A f j N) (B : Formula (m+1)) :
    Inputs n (Context.add B (Context.image Formula.raise Γ)) w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc := by
  exact ⟨of_eq (omega_rename w Fin.castSucc) (under h.hw B), of_eq (successor_rename A a Fin.castSucc) (under h.hs B),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under h.hf B),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+1) j Fin.castSucc) (under h.hj B),
    of_eq (formulaCode_rename w N a f Fin.castSucc) (under h.hn B)⟩
private theorem underInputs2 {n m} {Γ : Context m} {w a A f j N : Fin m}
    (h : Inputs n Γ w a A f j N) (B : Formula (m+2)) :
    Inputs n (Context.add B (raisedContext 2 Γ)) (old 2 w) (old 2 a) (old 2 A) (old 2 f) (old 2 j) (old 2 N) := by
  exact ⟨of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 h.hw B),
    of_eq (successor_rename A a (old 2)) (HornBinderRules.under_body 2 h.hs B),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f (old 2)) (HornBinderRules.under_body 2 h.hf B),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+1) j (old 2)) (HornBinderRules.under_body 2 h.hj B),
    of_eq (formulaCode_rename w N a f (old 2)) (HornBinderRules.under_body 2 h.hn B)⟩

private theorem from_outputs {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w a A f j N z x C M O : Fin m) (h : Inputs n Γ w a A f j N)
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f z x))
    (hc : Derives Γ (ForcingConditionRebind.compiled w a f A j N C))
    (hm : Derives Γ (ForcingGuardCode.compiled false R w A f x M))
    (ho : Derives Γ (ForcingGuardCode.compiled true R w A f x O)) : Derives Γ (existsCompiled R w a A f j N) := by
  have hi : ShellInputs Γ w a A f M O C := ⟨h.hw,h.hs,.conjR (FormulaCodeProperties.guards w N a f h.hn),
    ForcingGuardCode.compiled_type false R w A f x M hm, ForcingGuardCode.compiled_type true R w A f x O ho,
    ForcingConditionRebind.compiled_type w a f A j N C hc⟩
  let T := shell w.castSucc a.castSucc A.castSucc f.castSucc M.castSucc O.castSucc C.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (shell_stage0 hZ w a A f M O C hi)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hh1 := of_eq (SyntaxMixedImageHead.head_rename w A f z x Fin.castSucc) (under hh T)
  have hc1 := of_eq (ForcingConditionRebind.compiled_rename w a f A j N C Fin.castSucc) (under hc T)
  have hm1 := of_eq (ForcingGuardCode.compiled_rename false R w A f x M Fin.castSucc) (under hm T)
  have ho1 := of_eq (ForcingGuardCode.compiled_rename true R w A f x O Fin.castSucc) (under ho T)
  let v : Fin 5 → Fin (m+1) := Fin.cases z.castSucc (Fin.cases x.castSucc (Fin.cases C.castSucc (SetLanguage.args2 M.castSucc O.castSucc)))
  have hd : Derives Δ (data R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m) v) :=
    .conjI hh1 (.conjI hc1 (.conjI hm1 (.conjI ho1 hT)))
  have hb : Derives Δ (existsMany 5 (body R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m))) := by
    apply HornBinderRules.intro_many 5 _ v
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]) hd
  have hj := of_eq (SyntaxNumeralSyntax.numeral_rename (n+1) j Fin.castSucc) (under h.hj T)
  have hq : Derives Δ (compiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)) := .conjI hj hb
  have hresult : Derives Δ (existsCompiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq
  exact of_eq (existsCompiled_rename R w a A f j N Fin.castSucc).symm hresult

private theorem from_member {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w a A f j N z x C M: Fin m) (h : Inputs n Γ w a A f j N)
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f z x))
    (hc : Derives Γ (ForcingConditionRebind.compiled w a f A j N C))
    (hm : Derives Γ (ForcingGuardCode.compiled false R w A f x M))
    : Derives Γ (existsCompiled R w a A f j N) := by
  let T := ForcingGuardCode.compiled true R w.castSucc A.castSucc f.castSucc x.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingGuardCode.total hZ true R w A f x h.hw h.hf (.conjR (.conjR hh)))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hh1 := of_eq (SyntaxMixedImageHead.head_rename w A f z x Fin.castSucc) (under hh T)
  have hc1 := of_eq (ForcingConditionRebind.compiled_rename w a f A j N C Fin.castSucc) (under hc T)
  have hm1 := of_eq (ForcingGuardCode.compiled_rename false R w A f x M Fin.castSucc) (under hm T)
  have ho := from_outputs (ZFContext.under hZ T) R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc z.castSucc x.castSucc C.castSucc M.castSucc (Fin.last m) (underInputs h T) hh1 hc1 hm1 hT
  exact of_eq (existsCompiled_rename R w a A f j N Fin.castSucc).symm ho

private theorem from_child {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w a A f j N z x C: Fin m) (h : Inputs n Γ w a A f j N)
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f z x))
    (hc : Derives Γ (ForcingConditionRebind.compiled w a f A j N C))
    : Derives Γ (existsCompiled R w a A f j N) := by
  let T := ForcingGuardCode.compiled false R w.castSucc A.castSucc f.castSucc x.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingGuardCode.total hZ false R w A f x h.hw h.hf (.conjR (.conjR hh)))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hh1 := of_eq (SyntaxMixedImageHead.head_rename w A f z x Fin.castSucc) (under hh T)
  have hc1 := of_eq (ForcingConditionRebind.compiled_rename w a f A j N C Fin.castSucc) (under hc T)
  have ho := from_member (ZFContext.under hZ T) R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc z.castSucc x.castSucc C.castSucc (Fin.last m) (underInputs h T) hh1 hc1 hT
  exact of_eq (existsCompiled_rename R w a A f j N Fin.castSucc).symm ho

private theorem from_head {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w a A f j N z x: Fin m) (h : Inputs n Γ w a A f j N)
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f z x))
    : Derives Γ (existsCompiled R w a A f j N) := by
  let T := ForcingConditionRebind.compiled w.castSucc a.castSucc f.castSucc A.castSucc j.castSucc N.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingConditionRebind.total hZ w a f A j N h.hw h.hs h.hn)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hh1 := of_eq (SyntaxMixedImageHead.head_rename w A f z x Fin.castSucc) (under hh T)
  have ho := from_child (ZFContext.under hZ T) R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc z.castSucc x.castSucc (Fin.last m) (underInputs h T) hh1 hT
  exact of_eq (existsCompiled_rename R w a A f j N Fin.castSucc).symm ho

/-- Complete literal negative step on an arbitrary internal child formula code.
All outputs, guards, heads, lists and constructor executions are constructed. -/
theorem total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w a A f j N : Fin m) (hw : Derives Γ (omega w)) (hs : Derives Γ (successor A a))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j))
    (hN : Derives Γ (formulaCode w N a f)) : Derives Γ (existsCompiled R w a A f j N) := by
  let B := SyntaxMixedImageHead.head (old 2 w) (old 2 A) (old 2 f) (slot 2 0) (slot 2 1)
  let Δ := Context.add B (raisedContext 2 Γ)
  have hc := Derives.conjR (FormulaCodeProperties.guards w N a f hN)
  apply HornBinderRules.eliminate_many 2 B _ (SyntaxMixedImageHead.exists_head hZ w a A f hw (.conjL hc) (.conjR hc) hs)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := from_head (HornBinderRules.zf_body 2 hZ B) R (old 2 w) (old 2 a) (old 2 A) (old 2 f) (old 2 j) (old 2 N)
    (slot 2 0) (slot 2 1) (underInputs2 ⟨hw,hs,hf,hj,hN⟩ B) hB
  exact of_eq (existsCompiled_rename R w a A f j N (old 2)).symm ho

theorem compiled_type {n m} {Γ : Context m} (R : Source.Formula (n+2)) (w a A f j N Q : Fin m)
    (hq : Derives Γ (compiled R w a A f j N Q)) : Derives Γ (formulaCode w Q a f) := by
  let B := body R w a A f j N Q
  let Δ := Context.add B (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 B _ (.conjR hq)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w Q a f (old 5)).symm
    (shell_type (old 5 w) (old 5 a) (old 5 A) (old 5 f) (slot 5 3) (slot 5 4) (slot 5 2) (old 5 Q)
      (.conjR (.conjR (.conjR (.conjR hB)))))


private theorem guard_input_subst {n m} {Γ : Context m} (order : Bool) (R : Source.Formula (n+2))
    (w A f x y Q : Fin m) (he : Derives Γ (.equal x y)) (h : Derives Γ (ForcingGuardCode.compiled order R w A f x Q)) :
    Derives Γ (ForcingGuardCode.compiled order R w A f y Q) := by
  let P := ForcingGuardCode.compiled order R w.castSucc A.castSucc f.castSucc (Fin.last m) Q.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, ForcingGuardCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, ForcingGuardCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))

private theorem shell_inputs_subst {m} {Γ : Context m} (w a A f M O C Q U V D : Fin m)
    (hM : Derives Γ (.equal M U)) (hO : Derives Γ (.equal O V)) (hC : Derives Γ (.equal C D))
    (h : Derives Γ (shell w a A f M O C Q)) : Derives Γ (shell w a A f U V D Q) := by
  let P := shell w.castSucc a.castSucc A.castSucc f.castSucc (Fin.last m) O.castSucc C.castSucc Q.castSucc
  have h1 : Derives Γ (shell w a A f U O C Q) :=
    of_eq (by simp only [P, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P hM (of_eq (by simp only [P, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  let S := shell w.castSucc a.castSucc A.castSucc f.castSucc U.castSucc (Fin.last m) C.castSucc Q.castSucc
  have h2 : Derives Γ (shell w a A f U V C Q) :=
    of_eq (by simp only [S, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst S hO (of_eq (by simp only [S, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h1))
  let T := shell w.castSucc a.castSucc A.castSucc f.castSucc U.castSucc V.castSucc (Fin.last m) Q.castSucc
  exact of_eq (by simp only [T, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst T hC (of_eq (by simp only [T, Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h2))

private theorem data_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w a A f j N Q V : Fin m) (xs ys : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (data R w a A f j N Q xs)) (hy : Derives Γ (data R w a A f j N V ys)) : Derives Γ (.equal Q V) := by
  have hhx := Derives.conjL hx
  have hhy := Derives.conjL hy
  have hz := OmegaUniversal.empty_unique (xs 0) (ys 0) (ZFContext.arithmetic hZ).base.extensionality (.conjL hhx) (.conjL hhy)
  have hcode := AbstractVariableIndex.code_index_subst true w (xs 0) (ys 0) (xs 1) hz (.conjL (.conjR hhx))
  have he := SyntaxVariables.unique hZ true w (ys 0) (xs 1) (ys 1) hw hcode (.conjL (.conjR hhy))
  have hc := ForcingConditionRebind.unique hZ w a f A j N (xs 2) (ys 2) hw (.conjL (.conjR hx)) (.conjL (.conjR hy))
  have hm1 := guard_input_subst false R w A f (xs 1) (ys 1) (xs 3) he (.conjL (.conjR (.conjR hx)))
  have hm := ForcingGuardCode.unique hZ false R w A f (ys 1) (xs 3) (ys 3) hw hm1 (.conjL (.conjR (.conjR hy)))
  have ho1 := guard_input_subst true R w A f (xs 1) (ys 1) (xs 4) he (.conjL (.conjR (.conjR (.conjR hx))))
  have ho := ForcingGuardCode.unique hZ true R w A f (ys 1) (xs 4) (ys 4) hw ho1 (.conjL (.conjR (.conjR (.conjR hy))))
  have hq := shell_inputs_subst w a A f (xs 3) (xs 4) (xs 2) Q (ys 3) (ys 4) (ys 2) hm ho hc
    (.conjR (.conjR (.conjR (.conjR hx))))
  exact shell_unique hZ w a A f (ys 3) (ys 4) (ys 2) Q V hw hq (.conjR (.conjR (.conjR (.conjR hy))))

/-- No shared canonical execution is assumed for either candidate. -/
theorem unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w a A f j N Q V : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (compiled R w a A f j N Q)) (hv : Derives Γ (compiled R w a A f j N V)) : Derives Γ (.equal Q V) := by
  let B := body R w a A f j N Q
  let Δ := Context.add B (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 B _ (.conjR hq)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hv1 := of_eq (compiled_rename R w a A f j N V (old 5)) (HornBinderRules.under_body 5 hv B)
  let T := body R (old 5 w) (old 5 a) (old 5 A) (old 5 f) (old 5 j) (old 5 N) (old 5 V)
  let Ξ := Context.add T (raisedContext 5 Δ)
  apply HornBinderRules.eliminate_many 5 T _ (.conjR hv1)
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hw2 : Derives Ξ (omega (old 5 (old 5 w))) := of_eq (by simp only [omega_rename])
    (HornBinderRules.under_body 5 (HornBinderRules.under_body 5 hw B) T)
  have hx2 : Derives Ξ (data R (old 5 (old 5 w)) (old 5 (old 5 a)) (old 5 (old 5 A)) (old 5 (old 5 f))
      (old 5 (old 5 j)) (old 5 (old 5 N)) (old 5 (old 5 Q)) (fun i => old 5 (slot 5 i))) :=
    of_eq (by simp only [B, body, data_rename]) (HornBinderRules.under_body 5 hB T)
  exact data_unique (HornBinderRules.zf_body 5 (HornBinderRules.zf_body 5 hZ B) T) R
    (old 5 (old 5 w)) (old 5 (old 5 a)) (old 5 (old 5 A)) (old 5 (old 5 f))
    (old 5 (old 5 j)) (old 5 (old 5 N)) (old 5 (old 5 Q)) (old 5 (old 5 V))
    (fun i => old 5 (slot 5 i)) (slot 5) hw2 hx2 hT

def uniqueOutput {n m} (R : Source.Formula (n+2)) (w a A f j N Q : Fin m) : Formula m := .all
  ((compiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)).imp (.equal (Fin.last m) Q.castSucc))
private theorem uniqueOutput_rename {n m l} (R : Source.Formula (n+2)) (w a A f j N Q : Fin m) (r : Fin m → Fin l) :
    (uniqueOutput R w a A f j N Q).rename r = uniqueOutput R (r w) (r a) (r A) (r f) (r j) (r N) (r Q) := by
  simp only [uniqueOutput, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
private theorem unique_output {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w a A f j N Q : Fin m) (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled R w a A f j N Q)) :
    Derives Γ (uniqueOutput R w a A f j N Q) := by
  apply Derives.allI
  apply Derives.impI
  let B := compiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)
  exact unique (ZFContext.under hZ B) R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m) Q.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw B)) (.hyp (Or.inl rfl))
    (of_eq (compiled_rename R w a A f j N Q Fin.castSucc) (under hq B))

def fiber {n m} (R : Source.Formula (n+2)) (w a A f j N : Fin m) : Formula m := .ex
  ((compiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)).conj
    ((formulaCode w.castSucc (Fin.last m) a.castSucc f.castSucc).conj
      (uniqueOutput R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m))))
private theorem fiber_rename {n m l} (R : Source.Formula (n+2)) (w a A f j N : Fin m) (r : Fin m → Fin l) :
    (fiber R w a A f j N).rename r = fiber R (r w) (r a) (r A) (r f) (r j) (r N) := by
  simp only [fiber, Formula.rename, compiled_rename, formulaCode_rename, uniqueOutput_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w a A f j N : Fin m) (hw : Derives Γ (omega w)) (hs : Derives Γ (successor A a))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j))
    (hN : Derives Γ (formulaCode w N a f)) : Derives Γ (fiber R w a A f j N) := by
  let B := compiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (total hZ R w a A f j N hw hs hf hj hN)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := compiled_type R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m) hB
  have hu := unique_output (ZFContext.under hZ B) R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw B)) hB
  have ho : Derives Δ (fiber R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [B, Formula.instantiate, Formula.rename, compiled_rename, formulaCode_rename,
      uniqueOutput_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hB (.conjI ht hu))
  exact of_eq (fiber_rename R w a A f j N Fin.castSucc).symm ho

def sentence {n m} (R : Source.Formula (n+2)) (w a A f j N : Fin m) : Source.Sentence :=
  ((omega w).imp ((successor A a).imp ((SyntaxNumeralSyntax.numeral (n+2) f).imp
    ((SyntaxNumeralSyntax.numeral (n+1) j).imp ((formulaCode w N a f).imp (fiber R w a A f j N)))))).close

def uniqueSentence {n m} (R : Source.Formula (n+2)) (w a A f j N Q V : Fin m) : Source.Sentence :=
  ((omega w).imp ((compiled R w a A f j N Q).imp ((compiled R w a A f j N V).imp (.equal Q V)))).close

theorem kernel_certificate {n m} (R : Source.Formula (n+2)) (w a A f j N : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R w a A f j N)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact fiber_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _)
    R w a A f j N (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem unique_kernel_certificate {n m} (R : Source.Formula (n+2)) (w a A f j N Q V : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (uniqueSentence R w a A f j N Q V)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact unique (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _)
    R w a A f j N Q V (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

/-- The actual raw forall body of this complete negative fragment. The
source compiled judgment retains its actual guards and condition rebinding. -/
def bodyOutput {m} (w A f Q : Fin m) : Formula m := .ex
  ((SyntaxLogicalSyntax.singleCode 9 w.castSucc (Fin.last m) Q.castSucc).conj
    (formulaCode w.castSucc (Fin.last m) A.castSucc f.castSucc))

theorem bodyOutput_rename {m l} (w A f Q : Fin m) (r : Fin m → Fin l) :
    (bodyOutput w A f Q).rename r = bodyOutput (r w) (r A) (r f) (r Q) := by
  simp only [bodyOutput, Formula.rename, SyntaxLogicalSyntax.singleCode_rename, formulaCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Read the real outer forall and its typed body from the ACTUAL full
negative compilation; no body code, history or local answer is supplied. -/
theorem body_output {n m} {Γ : Context m} (R : Source.Formula (n+2)) (w a A f j N Q : Fin m)
    (hc : Derives Γ (compiled R w a A f j N Q)) : Derives Γ (bodyOutput w A f Q) := by
  let E := body R w a A f j N Q
  let Δ := Context.add E (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 E _ (.conjR hc)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let B := shellBody (old 5 w) (old 5 a) (old 5 A) (old 5 f) (slot 5 3) (slot 5 4) (slot 5 2) (old 5 Q)
  let Ξ := Context.add B (raisedContext 4 Δ)
  have hout : Derives Δ (bodyOutput (old 5 w) (old 5 A) (old 5 f) (old 5 Q)) := by
    apply HornBinderRules.eliminate_many 4 B _ (.conjR (.conjR (.conjR (.conjR hE))))
    have hB : Derives Ξ B := .hyp (Or.inl rfl)
    have hlast := Derives.conjL (.conjR (.conjR (.conjR hB)))
    have hall := Derives.conjR (.conjR (.conjR (.conjR hB)))
    have result : Derives Ξ (bodyOutput (old 4 (old 5 w)) (old 4 (old 5 A)) (old 4 (old 5 f)) (old 4 (old 5 Q))) := by
      apply Derives.exI (slot 4 3)
      exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxLogicalSyntax.singleCode_rename,
        formulaCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl) (.conjI (.conjL hall) (.conjR hlast))
    exact of_eq (bodyOutput_rename (old 5 w) (old 5 A) (old 5 f) (old 5 Q) (old 4)).symm result
  exact of_eq (bodyOutput_rename w A f Q (old 5)).symm hout

end PPAC.Migration.ForcingNegCode
