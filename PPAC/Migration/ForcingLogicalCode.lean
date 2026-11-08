import PPAC.Migration.ForcingNegCode
import PPAC.Migration.ForcingExistCode

/-! Exact remaining native logical operations for the internal forcing-code
interpreter. The fixed source toBasic normalizations are preserved: OR becomes
NEG(AND(NEG left,NEG right)), IMP becomes NEG(AND(left,NEG right)), IFF is
the conjunction of the two implications, and ALL becomes NEG(EX(NEG child)).
Every intermediate is an object witness, constructed using the already proved
negative/existential operations and native AND. This is not yet a complete raw
recursive interpreter, uniform coded axiom forcing or the final Proof/Con. -/
namespace PPAC.Migration.ForcingLogicalCode
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
set_option maxRecDepth 16384

private def andCode {m} (w a f N M Q : Fin m) : Formula m :=
  FormulaCodeConstructSyntax.typedAt 2 5 w (SyntaxAtomSyntax.two N M) Q a f
private theorem andCode_rename {m l} (w a f N M Q : Fin m) (r : Fin m → Fin l) :
    (andCode w a f N M Q).rename r = andCode (r w) (r a) (r f) (r N) (r M) (r Q) := by
  simp only [andCode, FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]
private def existsAnd {m} (w a f N M : Fin m) : Formula m := .ex
  (andCode w.castSucc a.castSucc f.castSucc N.castSucc M.castSucc (Fin.last m))
private theorem existsAnd_rename {m l} (w a f N M : Fin m) (r : Fin m → Fin l) :
    (existsAnd w a f N M).rename r = existsAnd (r w) (r a) (r f) (r N) (r M) := by
  simp only [existsAnd, Formula.rename, andCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
private theorem and_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a f N M : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (formulaCode w N a f)) (hm : Derives Γ (formulaCode w M a f)) :
    Derives Γ (existsAnd w a f N M) := by
  have he := FormulaCodeConstruct.exists_of_fiber 2 5 w (SyntaxAtomSyntax.two N M) a f
    (FormulaCodeConstructors.binary0 hZ w a f N M hw (.conjI (.conjR (FormulaCodeProperties.guards w N a f hn)) (.conjI hn hm)))
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (andCode w.castSucc a.castSucc f.castSucc N.castSucc M.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ho : Derives Δ (existsAnd w.castSucc a.castSucc f.castSucc N.castSucc M.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, andCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR hT)
  exact of_eq (existsAnd_rename w a f N M Fin.castSucc).symm ho
private theorem and_type {m} {Γ : Context m} (w a f N M Q : Fin m)
    (h : Derives Γ (andCode w a f N M Q)) : Derives Γ (formulaCode w Q a f) := .conjR h
private theorem and_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a f N M Q V : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (andCode w a f N M Q)) (hv : Derives Γ (andCode w a f N M V)) :
    Derives Γ (.equal Q V) := SyntaxConstructors.unique hZ 2 5 w (SyntaxAtomSyntax.two N M) Q V hw (.conjL hq) (.conjL hv)

private theorem and_inputs_subst {m} {Γ : Context m} (w a f N M Q Nnew Mnew : Fin m)
    (e0 : Derives Γ (.equal N Nnew))
    (e1 : Derives Γ (.equal M Mnew))
    (h : Derives Γ (andCode w a f N M Q)) : Derives Γ (andCode w a f Nnew Mnew Q) := by
  let P0 := andCode w.castSucc a.castSucc f.castSucc (Fin.last m) M.castSucc Q.castSucc
  have h0 : Derives Γ (andCode w a f Nnew M Q) :=
    of_eq (by simp only [P0, Formula.instantiate, andCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P0 e0 (of_eq (by simp only [P0, Formula.instantiate, andCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  let P1 := andCode w.castSucc a.castSucc f.castSucc Nnew.castSucc (Fin.last m) Q.castSucc
  have h1 : Derives Γ (andCode w a f Nnew Mnew Q) :=
    of_eq (by simp only [P1, Formula.instantiate, andCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P1 e1 (of_eq (by simp only [P1, Formula.instantiate, andCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h0))
  exact h1

private theorem neg_inputs_subst {n m} {Γ : Context m} (R : Source.Formula (n+2)) (w a A f j N Q Nnew : Fin m)
    (e0 : Derives Γ (.equal N Nnew))
    (h : Derives Γ (ForcingNegCode.compiled R w a A f j N Q)) : Derives Γ (ForcingNegCode.compiled R w a A f j Nnew Q) := by
  let P0 := ForcingNegCode.compiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc (Fin.last m) Q.castSucc
  have h0 : Derives Γ (ForcingNegCode.compiled R w a A f j Nnew Q) :=
    of_eq (by simp only [P0, Formula.instantiate, ForcingNegCode.compiled_rename R, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P0 e0 (of_eq (by simp only [P0, Formula.instantiate, ForcingNegCode.compiled_rename R, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  exact h0

private theorem ex_inputs_subst {n m} {Γ : Context m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q Nnew : Fin m)
    (e0 : Derives Γ (.equal N Nnew))
    (h : Derives Γ (ForcingExistCode.compiled R H w a A B C f j N Q)) : Derives Γ (ForcingExistCode.compiled R H w a A B C f j Nnew Q) := by
  let P0 := ForcingExistCode.compiled R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc (Fin.last m) Q.castSucc
  have h0 : Derives Γ (ForcingExistCode.compiled R H w a A B C f j Nnew Q) :=
    of_eq (by simp only [P0, Formula.instantiate, ForcingExistCode.compiled_rename R H, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P0 e0 (of_eq (by simp only [P0, Formula.instantiate, ForcingExistCode.compiled_rename R H, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  exact h0

private structure BinaryInputs {m} (n : Nat) (Γ : Context m) (w a A f j N M : Fin m) : Prop where
  hw : Derives Γ (omega w)
  hs : Derives Γ (successor A a)
  hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)
  hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j)
  hn : Derives Γ (formulaCode w N a f)
  hm : Derives Γ (formulaCode w M a f)
private theorem underBinaryInputs {n m} {Γ : Context m} {w a A f j N M : Fin m}
    (h : BinaryInputs n Γ w a A f j N M) (T : Formula (m+1)) :
    BinaryInputs n (Context.add T (Context.image Formula.raise Γ)) w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc := by
  exact ⟨of_eq (omega_rename w Fin.castSucc) (under h.hw T),
    of_eq (successor_rename A a Fin.castSucc) (under h.hs T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under h.hf T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+1) j Fin.castSucc) (under h.hj T),
    of_eq (formulaCode_rename w N a f Fin.castSucc) (under h.hn T),
    of_eq (formulaCode_rename w M a f Fin.castSucc) (under h.hm T)⟩

private structure AllInputs {m} (n : Nat) (Γ : Context m) (w a A B C f j N : Fin m) : Prop where
  hw : Derives Γ (omega w)
  ha : Derives Γ (Formula.mem a w)
  hA : Derives Γ (successor A a)
  hB : Derives Γ (successor B A)
  hC : Derives Γ (successor C B)
  hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)
  hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j)
  hn : Derives Γ (formulaCode w N A f)
private theorem underAllInputs {n m} {Γ : Context m} {w a A B C f j N : Fin m}
    (h : AllInputs n Γ w a A B C f j N) (T : Formula (m+1)) :
    AllInputs n (Context.add T (Context.image Formula.raise Γ)) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc := by
  exact ⟨of_eq (omega_rename w Fin.castSucc) (under h.hw T),
    under h.ha T,
    of_eq (successor_rename A a Fin.castSucc) (under h.hA T),
    of_eq (successor_rename B A Fin.castSucc) (under h.hB T),
    of_eq (successor_rename C B Fin.castSucc) (under h.hC T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under h.hf T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (n+1) j Fin.castSucc) (under h.hj T),
    of_eq (formulaCode_rename w N A f Fin.castSucc) (under h.hn T)⟩

private def impData {n m} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) (v : Fin 2 → Fin m) : Formula m :=
  (ForcingNegCode.compiled R w a A f j M (v 0)).conj ((andCode w a f N (v 0) (v 1)).conj (ForcingNegCode.compiled R w a A f j (v 1) Q))
private theorem impData_rename {n m l} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) (v : Fin 2 → Fin m) (r : Fin m → Fin l) :
    (impData R w a A f j N M Q v).rename r = impData R (r w) (r a) (r A) (r f) (r j) (r N) (r M) (r Q) (fun i => r (v i)) := by
  simp only [impData, Formula.rename, ForcingNegCode.compiled_rename, andCode_rename]
private def impBody {n m} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) : Formula (m+2) :=
  impData R (old 2 w) (old 2 a) (old 2 A) (old 2 f) (old 2 j) (old 2 N) (old 2 M) (old 2 Q) (slot 2)
private def impCode {n m} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) : Formula m := existsMany 2 (impBody R w a A f j N M Q)
private theorem impCode_rename {n m l} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) (r : Fin m → Fin l) :
    (impCode R w a A f j N M Q).rename r = impCode R (r w) (r a) (r A) (r f) (r j) (r N) (r M) (r Q) := by
  simp only [impCode, existsMany_rename, impBody, impData_rename, lift_old, lift_slot]
private def existsImp {n m} (R : Source.Formula (n+2)) (w a A f j N M : Fin m) : Formula m := .ex
  (impCode R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc (Fin.last m))
private theorem existsImp_rename {n m l} (R : Source.Formula (n+2)) (w a A f j N M : Fin m) (r : Fin m → Fin l) :
    (existsImp R w a A f j N M).rename r = existsImp R (r w) (r a) (r A) (r f) (r j) (r N) (r M) := by
  simp only [existsImp, Formula.rename, impCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem imp_stage2 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M u0 u1 : Fin m) (h : BinaryInputs n Γ w a A f j N M)
    (h0 : Derives Γ (ForcingNegCode.compiled R w a A f j M u0))
    (h1 : Derives Γ (andCode w a f N u0 u1))
    : Derives Γ (existsImp R w a A f j N M) := by
  let T := ForcingNegCode.compiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc u1.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingNegCode.total hZ R w a A f j u1 h.hw h.hs h.hf h.hj (and_type w a f N u0 u1 h1))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (ForcingNegCode.compiled_rename R w a A f j M u0 Fin.castSucc) (under h0 T)
  have h1u := of_eq (andCode_rename w a f N u0 u1 Fin.castSucc) (under h1 T)
  let v : Fin 2 → Fin (m+1) := Fin.cases u0.castSucc (Fin.cases u1.castSucc (fun i => Fin.elim0 i))
  have hd : Derives Δ (impData R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc (Fin.last m) v) := (.conjI h0u (.conjI h1u hT))
  have hc : Derives Δ (impCode R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc (Fin.last m)) := by
    apply HornBinderRules.intro_many 2 _ v
    exact of_eq (by simp only [impBody, impData_rename, assign_old, assign_slot]) hd
  have ho : Derives Δ (existsImp R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, impCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (existsImp_rename R w a A f j N M Fin.castSucc).symm ho

private theorem imp_stage1 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M u0 : Fin m) (h : BinaryInputs n Γ w a A f j N M)
    (h0 : Derives Γ (ForcingNegCode.compiled R w a A f j M u0))
    : Derives Γ (existsImp R w a A f j N M) := by
  let T := andCode w.castSucc a.castSucc f.castSucc N.castSucc u0.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (and_total hZ w a f N u0 h.hw h.hn (ForcingNegCode.compiled_type R w a A f j M u0 h0))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (ForcingNegCode.compiled_rename R w a A f j M u0 Fin.castSucc) (under h0 T)
  have ho := imp_stage2 (ZFContext.under hZ T) R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc u0.castSucc (Fin.last m) (underBinaryInputs h T) h0u hT
  exact of_eq (existsImp_rename R w a A f j N M Fin.castSucc).symm ho

private theorem imp_stage0 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M : Fin m) (h : BinaryInputs n Γ w a A f j N M)
    : Derives Γ (existsImp R w a A f j N M) := by
  let T := ForcingNegCode.compiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc M.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingNegCode.total hZ R w a A f j M h.hw h.hs h.hf h.hj h.hm)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ho := imp_stage1 (ZFContext.under hZ T) R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc (Fin.last m) (underBinaryInputs h T)  hT
  exact of_eq (existsImp_rename R w a A f j N M Fin.castSucc).symm ho

private theorem imp_type {n m} {Γ : Context m} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m)
    (h : Derives Γ (impCode R w a A f j N M Q)) : Derives Γ (formulaCode w Q a f) := by
  let T := impBody R w a A f j N M Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ h
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w Q a f (old 2)).symm (ForcingNegCode.compiled_type R (old 2 w) (old 2 a) (old 2 A) (old 2 f) (old 2 j) (slot 2 1) (old 2 Q) (.conjR (.conjR hT)))

private theorem impData_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M Q V : Fin m) (xs ys : Fin 2 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (impData R w a A f j N M Q xs)) (hy : Derives Γ (impData R w a A f j N M V ys)) : Derives Γ (.equal Q V) := by
  have e0 := ForcingNegCode.unique hZ R w a A f j M (xs 0) (ys 0) hw (.conjL hx) (.conjL hy)
  have h1 := and_inputs_subst w a f N (xs 0) (xs 1) N (ys 0) (.eqRefl N) e0 (.conjL (.conjR hx))
  have e1 := and_unique hZ w a f N (ys 0) (xs 1) (ys 1) hw h1 (.conjL (.conjR hy))
  have h2 := neg_inputs_subst R w a A f j (xs 1) Q (ys 1) e1 (.conjR (.conjR hx))
  have e2 := ForcingNegCode.unique hZ R w a A f j (ys 1) Q V hw h2 (.conjR (.conjR hy))
  exact e2

private theorem imp_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M Q V : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (impCode R w a A f j N M Q)) (hv : Derives Γ (impCode R w a A f j N M V)) : Derives Γ (.equal Q V) := by
  let T := impBody R w a A f j N M Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hv1 := of_eq (impCode_rename R w a A f j N M V (old 2)) (HornBinderRules.under_body 2 hv T)
  let U := impBody R (old 2 w) (old 2 a) (old 2 A) (old 2 f) (old 2 j) (old 2 N) (old 2 M) (old 2 V)
  let Ξ := Context.add U (raisedContext 2 Δ)
  apply HornBinderRules.eliminate_many 2 U _ hv1
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hw2 : Derives Ξ (omega (old 2 (old 2 w))) := of_eq (by simp only [omega_rename])
    (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hw T) U)
  have hx2 : Derives Ξ (impData R (old 2 (old 2 w)) (old 2 (old 2 a)) (old 2 (old 2 A)) (old 2 (old 2 f)) (old 2 (old 2 j)) (old 2 (old 2 N)) (old 2 (old 2 M)) (old 2 (old 2 Q)) (fun i => old 2 (slot 2 i))) :=
    of_eq (by simp only [T, impBody, impData_rename]) (HornBinderRules.under_body 2 hT U)
  exact impData_unique (HornBinderRules.zf_body 2 (HornBinderRules.zf_body 2 hZ T) U) R
    (old 2 (old 2 w)) (old 2 (old 2 a)) (old 2 (old 2 A)) (old 2 (old 2 f)) (old 2 (old 2 j)) (old 2 (old 2 N)) (old 2 (old 2 M)) (old 2 (old 2 Q)) (old 2 (old 2 V)) (fun i => old 2 (slot 2 i)) (slot 2) hw2 hx2 hU

private theorem imp_inputs_subst {n m} {Γ : Context m} (R : Source.Formula (n+2)) (w a A f j N M Q Nnew Mnew : Fin m)
    (e0 : Derives Γ (.equal N Nnew))
    (e1 : Derives Γ (.equal M Mnew))
    (h : Derives Γ (impCode R w a A f j N M Q)) : Derives Γ (impCode R w a A f j Nnew Mnew Q) := by
  let P0 := impCode R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc (Fin.last m) M.castSucc Q.castSucc
  have h0 : Derives Γ (impCode R w a A f j Nnew M Q) :=
    of_eq (by simp only [P0, Formula.instantiate, impCode_rename R, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P0 e0 (of_eq (by simp only [P0, Formula.instantiate, impCode_rename R, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  let P1 := impCode R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc Nnew.castSucc (Fin.last m) Q.castSucc
  have h1 : Derives Γ (impCode R w a A f j Nnew Mnew Q) :=
    of_eq (by simp only [P1, Formula.instantiate, impCode_rename R, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P1 e1 (of_eq (by simp only [P1, Formula.instantiate, impCode_rename R, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h0))
  exact h1

private def orData {n m} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) (v : Fin 3 → Fin m) : Formula m :=
  (ForcingNegCode.compiled R w a A f j N (v 0)).conj ((ForcingNegCode.compiled R w a A f j M (v 1)).conj ((andCode w a f (v 0) (v 1) (v 2)).conj (ForcingNegCode.compiled R w a A f j (v 2) Q)))
private theorem orData_rename {n m l} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) (v : Fin 3 → Fin m) (r : Fin m → Fin l) :
    (orData R w a A f j N M Q v).rename r = orData R (r w) (r a) (r A) (r f) (r j) (r N) (r M) (r Q) (fun i => r (v i)) := by
  simp only [orData, Formula.rename, ForcingNegCode.compiled_rename, andCode_rename]
private def orBody {n m} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) : Formula (m+3) :=
  orData R (old 3 w) (old 3 a) (old 3 A) (old 3 f) (old 3 j) (old 3 N) (old 3 M) (old 3 Q) (slot 3)
private def orCode {n m} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) : Formula m := existsMany 3 (orBody R w a A f j N M Q)
private theorem orCode_rename {n m l} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) (r : Fin m → Fin l) :
    (orCode R w a A f j N M Q).rename r = orCode R (r w) (r a) (r A) (r f) (r j) (r N) (r M) (r Q) := by
  simp only [orCode, existsMany_rename, orBody, orData_rename, lift_old, lift_slot]
private def existsOr {n m} (R : Source.Formula (n+2)) (w a A f j N M : Fin m) : Formula m := .ex
  (orCode R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc (Fin.last m))
private theorem existsOr_rename {n m l} (R : Source.Formula (n+2)) (w a A f j N M : Fin m) (r : Fin m → Fin l) :
    (existsOr R w a A f j N M).rename r = existsOr R (r w) (r a) (r A) (r f) (r j) (r N) (r M) := by
  simp only [existsOr, Formula.rename, orCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem or_stage3 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M u0 u1 u2 : Fin m) (h : BinaryInputs n Γ w a A f j N M)
    (h0 : Derives Γ (ForcingNegCode.compiled R w a A f j N u0))
    (h1 : Derives Γ (ForcingNegCode.compiled R w a A f j M u1))
    (h2 : Derives Γ (andCode w a f u0 u1 u2))
    : Derives Γ (existsOr R w a A f j N M) := by
  let T := ForcingNegCode.compiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc u2.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingNegCode.total hZ R w a A f j u2 h.hw h.hs h.hf h.hj (and_type w a f u0 u1 u2 h2))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (ForcingNegCode.compiled_rename R w a A f j N u0 Fin.castSucc) (under h0 T)
  have h1u := of_eq (ForcingNegCode.compiled_rename R w a A f j M u1 Fin.castSucc) (under h1 T)
  have h2u := of_eq (andCode_rename w a f u0 u1 u2 Fin.castSucc) (under h2 T)
  let v : Fin 3 → Fin (m+1) := Fin.cases u0.castSucc (Fin.cases u1.castSucc (Fin.cases u2.castSucc (fun i => Fin.elim0 i)))
  have hd : Derives Δ (orData R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc (Fin.last m) v) := (.conjI h0u (.conjI h1u (.conjI h2u hT)))
  have hc : Derives Δ (orCode R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc (Fin.last m)) := by
    apply HornBinderRules.intro_many 3 _ v
    exact of_eq (by simp only [orBody, orData_rename, assign_old, assign_slot]) hd
  have ho : Derives Δ (existsOr R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, orCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (existsOr_rename R w a A f j N M Fin.castSucc).symm ho

private theorem or_stage2 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M u0 u1 : Fin m) (h : BinaryInputs n Γ w a A f j N M)
    (h0 : Derives Γ (ForcingNegCode.compiled R w a A f j N u0))
    (h1 : Derives Γ (ForcingNegCode.compiled R w a A f j M u1))
    : Derives Γ (existsOr R w a A f j N M) := by
  let T := andCode w.castSucc a.castSucc f.castSucc u0.castSucc u1.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (and_total hZ w a f u0 u1 h.hw (ForcingNegCode.compiled_type R w a A f j N u0 h0) (ForcingNegCode.compiled_type R w a A f j M u1 h1))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (ForcingNegCode.compiled_rename R w a A f j N u0 Fin.castSucc) (under h0 T)
  have h1u := of_eq (ForcingNegCode.compiled_rename R w a A f j M u1 Fin.castSucc) (under h1 T)
  have ho := or_stage3 (ZFContext.under hZ T) R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc u0.castSucc u1.castSucc (Fin.last m) (underBinaryInputs h T) h0u h1u hT
  exact of_eq (existsOr_rename R w a A f j N M Fin.castSucc).symm ho

private theorem or_stage1 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M u0 : Fin m) (h : BinaryInputs n Γ w a A f j N M)
    (h0 : Derives Γ (ForcingNegCode.compiled R w a A f j N u0))
    : Derives Γ (existsOr R w a A f j N M) := by
  let T := ForcingNegCode.compiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc M.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingNegCode.total hZ R w a A f j M h.hw h.hs h.hf h.hj h.hm)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (ForcingNegCode.compiled_rename R w a A f j N u0 Fin.castSucc) (under h0 T)
  have ho := or_stage2 (ZFContext.under hZ T) R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc u0.castSucc (Fin.last m) (underBinaryInputs h T) h0u hT
  exact of_eq (existsOr_rename R w a A f j N M Fin.castSucc).symm ho

private theorem or_stage0 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M : Fin m) (h : BinaryInputs n Γ w a A f j N M)
    : Derives Γ (existsOr R w a A f j N M) := by
  let T := ForcingNegCode.compiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingNegCode.total hZ R w a A f j N h.hw h.hs h.hf h.hj h.hn)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ho := or_stage1 (ZFContext.under hZ T) R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc (Fin.last m) (underBinaryInputs h T)  hT
  exact of_eq (existsOr_rename R w a A f j N M Fin.castSucc).symm ho

private theorem or_type {n m} {Γ : Context m} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m)
    (h : Derives Γ (orCode R w a A f j N M Q)) : Derives Γ (formulaCode w Q a f) := by
  let T := orBody R w a A f j N M Q
  let Δ := Context.add T (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 T _ h
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w Q a f (old 3)).symm (ForcingNegCode.compiled_type R (old 3 w) (old 3 a) (old 3 A) (old 3 f) (old 3 j) (slot 3 2) (old 3 Q) (.conjR (.conjR (.conjR hT))))

private theorem orData_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M Q V : Fin m) (xs ys : Fin 3 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (orData R w a A f j N M Q xs)) (hy : Derives Γ (orData R w a A f j N M V ys)) : Derives Γ (.equal Q V) := by
  have e0 := ForcingNegCode.unique hZ R w a A f j N (xs 0) (ys 0) hw (.conjL hx) (.conjL hy)
  have e1 := ForcingNegCode.unique hZ R w a A f j M (xs 1) (ys 1) hw (.conjL (.conjR hx)) (.conjL (.conjR hy))
  have h2 := and_inputs_subst w a f (xs 0) (xs 1) (xs 2) (ys 0) (ys 1) e0 e1 (.conjL (.conjR (.conjR hx)))
  have e2 := and_unique hZ w a f (ys 0) (ys 1) (xs 2) (ys 2) hw h2 (.conjL (.conjR (.conjR hy)))
  have h3 := neg_inputs_subst R w a A f j (xs 2) Q (ys 2) e2 (.conjR (.conjR (.conjR hx)))
  have e3 := ForcingNegCode.unique hZ R w a A f j (ys 2) Q V hw h3 (.conjR (.conjR (.conjR hy)))
  exact e3

private theorem or_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M Q V : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (orCode R w a A f j N M Q)) (hv : Derives Γ (orCode R w a A f j N M V)) : Derives Γ (.equal Q V) := by
  let T := orBody R w a A f j N M Q
  let Δ := Context.add T (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hv1 := of_eq (orCode_rename R w a A f j N M V (old 3)) (HornBinderRules.under_body 3 hv T)
  let U := orBody R (old 3 w) (old 3 a) (old 3 A) (old 3 f) (old 3 j) (old 3 N) (old 3 M) (old 3 V)
  let Ξ := Context.add U (raisedContext 3 Δ)
  apply HornBinderRules.eliminate_many 3 U _ hv1
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hw2 : Derives Ξ (omega (old 3 (old 3 w))) := of_eq (by simp only [omega_rename])
    (HornBinderRules.under_body 3 (HornBinderRules.under_body 3 hw T) U)
  have hx2 : Derives Ξ (orData R (old 3 (old 3 w)) (old 3 (old 3 a)) (old 3 (old 3 A)) (old 3 (old 3 f)) (old 3 (old 3 j)) (old 3 (old 3 N)) (old 3 (old 3 M)) (old 3 (old 3 Q)) (fun i => old 3 (slot 3 i))) :=
    of_eq (by simp only [T, orBody, orData_rename]) (HornBinderRules.under_body 3 hT U)
  exact orData_unique (HornBinderRules.zf_body 3 (HornBinderRules.zf_body 3 hZ T) U) R
    (old 3 (old 3 w)) (old 3 (old 3 a)) (old 3 (old 3 A)) (old 3 (old 3 f)) (old 3 (old 3 j)) (old 3 (old 3 N)) (old 3 (old 3 M)) (old 3 (old 3 Q)) (old 3 (old 3 V)) (fun i => old 3 (slot 3 i)) (slot 3) hw2 hx2 hU

private def iffData {n m} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) (v : Fin 2 → Fin m) : Formula m :=
  (impCode R w a A f j N M (v 0)).conj ((impCode R w a A f j M N (v 1)).conj (andCode w a f (v 0) (v 1) Q))
private theorem iffData_rename {n m l} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) (v : Fin 2 → Fin m) (r : Fin m → Fin l) :
    (iffData R w a A f j N M Q v).rename r = iffData R (r w) (r a) (r A) (r f) (r j) (r N) (r M) (r Q) (fun i => r (v i)) := by
  simp only [iffData, Formula.rename, impCode_rename, andCode_rename]
private def iffBody {n m} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) : Formula (m+2) :=
  iffData R (old 2 w) (old 2 a) (old 2 A) (old 2 f) (old 2 j) (old 2 N) (old 2 M) (old 2 Q) (slot 2)
private def iffCode {n m} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) : Formula m := existsMany 2 (iffBody R w a A f j N M Q)
private theorem iffCode_rename {n m l} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) (r : Fin m → Fin l) :
    (iffCode R w a A f j N M Q).rename r = iffCode R (r w) (r a) (r A) (r f) (r j) (r N) (r M) (r Q) := by
  simp only [iffCode, existsMany_rename, iffBody, iffData_rename, lift_old, lift_slot]
private def existsIff {n m} (R : Source.Formula (n+2)) (w a A f j N M : Fin m) : Formula m := .ex
  (iffCode R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc (Fin.last m))
private theorem existsIff_rename {n m l} (R : Source.Formula (n+2)) (w a A f j N M : Fin m) (r : Fin m → Fin l) :
    (existsIff R w a A f j N M).rename r = existsIff R (r w) (r a) (r A) (r f) (r j) (r N) (r M) := by
  simp only [existsIff, Formula.rename, iffCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem iff_stage2 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M u0 u1 : Fin m) (h : BinaryInputs n Γ w a A f j N M)
    (h0 : Derives Γ (impCode R w a A f j N M u0))
    (h1 : Derives Γ (impCode R w a A f j M N u1))
    : Derives Γ (existsIff R w a A f j N M) := by
  let T := andCode w.castSucc a.castSucc f.castSucc u0.castSucc u1.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (and_total hZ w a f u0 u1 h.hw (imp_type R w a A f j N M u0 h0) (imp_type R w a A f j M N u1 h1))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (impCode_rename R w a A f j N M u0 Fin.castSucc) (under h0 T)
  have h1u := of_eq (impCode_rename R w a A f j M N u1 Fin.castSucc) (under h1 T)
  let v : Fin 2 → Fin (m+1) := Fin.cases u0.castSucc (Fin.cases u1.castSucc (fun i => Fin.elim0 i))
  have hd : Derives Δ (iffData R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc (Fin.last m) v) := (.conjI h0u (.conjI h1u hT))
  have hc : Derives Δ (iffCode R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc (Fin.last m)) := by
    apply HornBinderRules.intro_many 2 _ v
    exact of_eq (by simp only [iffBody, iffData_rename, assign_old, assign_slot]) hd
  have ho : Derives Δ (existsIff R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, iffCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (existsIff_rename R w a A f j N M Fin.castSucc).symm ho

private theorem iff_stage1 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M u0 : Fin m) (h : BinaryInputs n Γ w a A f j N M)
    (h0 : Derives Γ (impCode R w a A f j N M u0))
    : Derives Γ (existsIff R w a A f j N M) := by
  let T := impCode R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc M.castSucc N.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (imp_stage0 hZ R w a A f j M N ⟨h.hw,h.hs,h.hf,h.hj,h.hm,h.hn⟩)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (impCode_rename R w a A f j N M u0 Fin.castSucc) (under h0 T)
  have ho := iff_stage2 (ZFContext.under hZ T) R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc u0.castSucc (Fin.last m) (underBinaryInputs h T) h0u hT
  exact of_eq (existsIff_rename R w a A f j N M Fin.castSucc).symm ho

private theorem iff_stage0 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M : Fin m) (h : BinaryInputs n Γ w a A f j N M)
    : Derives Γ (existsIff R w a A f j N M) := by
  let T := impCode R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (imp_stage0 hZ R w a A f j N M ⟨h.hw,h.hs,h.hf,h.hj,h.hn,h.hm⟩)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ho := iff_stage1 (ZFContext.under hZ T) R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc (Fin.last m) (underBinaryInputs h T)  hT
  exact of_eq (existsIff_rename R w a A f j N M Fin.castSucc).symm ho

private theorem iff_type {n m} {Γ : Context m} (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m)
    (h : Derives Γ (iffCode R w a A f j N M Q)) : Derives Γ (formulaCode w Q a f) := by
  let T := iffBody R w a A f j N M Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ h
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w Q a f (old 2)).symm (and_type (old 2 w) (old 2 a) (old 2 f) (slot 2 0) (slot 2 1) (old 2 Q) (.conjR (.conjR hT)))

private theorem iffData_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M Q V : Fin m) (xs ys : Fin 2 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (iffData R w a A f j N M Q xs)) (hy : Derives Γ (iffData R w a A f j N M V ys)) : Derives Γ (.equal Q V) := by
  have e0 := imp_unique hZ R w a A f j N M (xs 0) (ys 0) hw (.conjL hx) (.conjL hy)
  have e1 := imp_unique hZ R w a A f j M N (xs 1) (ys 1) hw (.conjL (.conjR hx)) (.conjL (.conjR hy))
  have h2 := and_inputs_subst w a f (xs 0) (xs 1) Q (ys 0) (ys 1) e0 e1 (.conjR (.conjR hx))
  have e2 := and_unique hZ w a f (ys 0) (ys 1) Q V hw h2 (.conjR (.conjR hy))
  exact e2

private theorem iff_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A f j N M Q V : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (iffCode R w a A f j N M Q)) (hv : Derives Γ (iffCode R w a A f j N M V)) : Derives Γ (.equal Q V) := by
  let T := iffBody R w a A f j N M Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hv1 := of_eq (iffCode_rename R w a A f j N M V (old 2)) (HornBinderRules.under_body 2 hv T)
  let U := iffBody R (old 2 w) (old 2 a) (old 2 A) (old 2 f) (old 2 j) (old 2 N) (old 2 M) (old 2 V)
  let Ξ := Context.add U (raisedContext 2 Δ)
  apply HornBinderRules.eliminate_many 2 U _ hv1
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hw2 : Derives Ξ (omega (old 2 (old 2 w))) := of_eq (by simp only [omega_rename])
    (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hw T) U)
  have hx2 : Derives Ξ (iffData R (old 2 (old 2 w)) (old 2 (old 2 a)) (old 2 (old 2 A)) (old 2 (old 2 f)) (old 2 (old 2 j)) (old 2 (old 2 N)) (old 2 (old 2 M)) (old 2 (old 2 Q)) (fun i => old 2 (slot 2 i))) :=
    of_eq (by simp only [T, iffBody, iffData_rename]) (HornBinderRules.under_body 2 hT U)
  exact iffData_unique (HornBinderRules.zf_body 2 (HornBinderRules.zf_body 2 hZ T) U) R
    (old 2 (old 2 w)) (old 2 (old 2 a)) (old 2 (old 2 A)) (old 2 (old 2 f)) (old 2 (old 2 j)) (old 2 (old 2 N)) (old 2 (old 2 M)) (old 2 (old 2 Q)) (old 2 (old 2 V)) (fun i => old 2 (slot 2 i)) (slot 2) hw2 hx2 hU

private def allData {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m) (v : Fin 2 → Fin m) : Formula m :=
  (ForcingNegCode.compiled R w A B f j N (v 0)).conj ((ForcingExistCode.compiled R H w a A B C f j (v 0) (v 1)).conj (ForcingNegCode.compiled R w a A f j (v 1) Q))
private theorem allData_rename {n m l} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m) (v : Fin 2 → Fin m) (r : Fin m → Fin l) :
    (allData R H w a A B C f j N Q v).rename r = allData R H (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) (r Q) (fun i => r (v i)) := by
  simp only [allData, Formula.rename, ForcingNegCode.compiled_rename, ForcingExistCode.compiled_rename]
private def allBody {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m) : Formula (m+2) :=
  allData R H (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 f) (old 2 j) (old 2 N) (old 2 Q) (slot 2)
private def allCode {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m) : Formula m := existsMany 2 (allBody R H w a A B C f j N Q)
private theorem allCode_rename {n m l} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m) (r : Fin m → Fin l) :
    (allCode R H w a A B C f j N Q).rename r = allCode R H (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) (r Q) := by
  simp only [allCode, existsMany_rename, allBody, allData_rename, lift_old, lift_slot]
private def existsAll {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N : Fin m) : Formula m := .ex
  (allCode R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m))
private theorem existsAll_rename {n m l} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N : Fin m) (r : Fin m → Fin l) :
    (existsAll R H w a A B C f j N).rename r = existsAll R H (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) := by
  simp only [existsAll, Formula.rename, allCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem all_stage2 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N u0 u1 : Fin m) (h : AllInputs n Γ w a A B C f j N)
    (h0 : Derives Γ (ForcingNegCode.compiled R w A B f j N u0))
    (h1 : Derives Γ (ForcingExistCode.compiled R H w a A B C f j u0 u1))
    : Derives Γ (existsAll R H w a A B C f j N) := by
  let T := ForcingNegCode.compiled R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc u1.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingNegCode.total hZ R w a A f j u1 h.hw h.hA h.hf h.hj (ForcingExistCode.compiled_type R H w a A B C f j u0 u1 h1))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (ForcingNegCode.compiled_rename R w A B f j N u0 Fin.castSucc) (under h0 T)
  have h1u := of_eq (ForcingExistCode.compiled_rename R H w a A B C f j u0 u1 Fin.castSucc) (under h1 T)
  let v : Fin 2 → Fin (m+1) := Fin.cases u0.castSucc (Fin.cases u1.castSucc (fun i => Fin.elim0 i))
  have hd : Derives Δ (allData R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m) v) := (.conjI h0u (.conjI h1u hT))
  have hc : Derives Δ (allCode R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)) := by
    apply HornBinderRules.intro_many 2 _ v
    exact of_eq (by simp only [allBody, allData_rename, assign_old, assign_slot]) hd
  have ho : Derives Δ (existsAll R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, allCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (existsAll_rename R H w a A B C f j N Fin.castSucc).symm ho

private theorem all_stage1 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N u0 : Fin m) (h : AllInputs n Γ w a A B C f j N)
    (h0 : Derives Γ (ForcingNegCode.compiled R w A B f j N u0))
    : Derives Γ (existsAll R H w a A B C f j N) := by
  let T := ForcingExistCode.compiled R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc u0.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingExistCode.total hZ R H w a A B C f j u0 h.hw h.ha h.hA h.hB h.hC h.hf h.hj (ForcingNegCode.compiled_type R w A B f j N u0 h0))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h0u := of_eq (ForcingNegCode.compiled_rename R w A B f j N u0 Fin.castSucc) (under h0 T)
  have ho := all_stage2 (ZFContext.under hZ T) R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc u0.castSucc (Fin.last m) (underAllInputs h T) h0u hT
  exact of_eq (existsAll_rename R H w a A B C f j N Fin.castSucc).symm ho

private theorem all_stage0 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N : Fin m) (h : AllInputs n Γ w a A B C f j N)
    : Derives Γ (existsAll R H w a A B C f j N) := by
  let T := ForcingNegCode.compiled R w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingNegCode.total hZ R w A B f j N h.hw h.hB h.hf h.hj h.hn)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ho := all_stage1 (ZFContext.under hZ T) R H w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m) (underAllInputs h T)  hT
  exact of_eq (existsAll_rename R H w a A B C f j N Fin.castSucc).symm ho

private theorem all_type {n m} {Γ : Context m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m)
    (h : Derives Γ (allCode R H w a A B C f j N Q)) : Derives Γ (formulaCode w Q a f) := by
  let T := allBody R H w a A B C f j N Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ h
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w Q a f (old 2)).symm (ForcingNegCode.compiled_type R (old 2 w) (old 2 a) (old 2 A) (old 2 f) (old 2 j) (slot 2 1) (old 2 Q) (.conjR (.conjR hT)))

private theorem allData_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q V : Fin m) (xs ys : Fin 2 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (allData R H w a A B C f j N Q xs)) (hy : Derives Γ (allData R H w a A B C f j N V ys)) : Derives Γ (.equal Q V) := by
  have e0 := ForcingNegCode.unique hZ R w A B f j N (xs 0) (ys 0) hw (.conjL hx) (.conjL hy)
  have h1 := ex_inputs_subst R H w a A B C f j (xs 0) (xs 1) (ys 0) e0 (.conjL (.conjR hx))
  have e1 := ForcingExistCode.unique hZ R H w a A B C f j (ys 0) (xs 1) (ys 1) hw h1 (.conjL (.conjR hy))
  have h2 := neg_inputs_subst R w a A f j (xs 1) Q (ys 1) e1 (.conjR (.conjR hx))
  have e2 := ForcingNegCode.unique hZ R w a A f j (ys 1) Q V hw h2 (.conjR (.conjR hy))
  exact e2

private theorem all_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q V : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (allCode R H w a A B C f j N Q)) (hv : Derives Γ (allCode R H w a A B C f j N V)) : Derives Γ (.equal Q V) := by
  let T := allBody R H w a A B C f j N Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hv1 := of_eq (allCode_rename R H w a A B C f j N V (old 2)) (HornBinderRules.under_body 2 hv T)
  let U := allBody R H (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 f) (old 2 j) (old 2 N) (old 2 V)
  let Ξ := Context.add U (raisedContext 2 Δ)
  apply HornBinderRules.eliminate_many 2 U _ hv1
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hw2 : Derives Ξ (omega (old 2 (old 2 w))) := of_eq (by simp only [omega_rename])
    (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hw T) U)
  have hx2 : Derives Ξ (allData R H (old 2 (old 2 w)) (old 2 (old 2 a)) (old 2 (old 2 A)) (old 2 (old 2 B)) (old 2 (old 2 C)) (old 2 (old 2 f)) (old 2 (old 2 j)) (old 2 (old 2 N)) (old 2 (old 2 Q)) (fun i => old 2 (slot 2 i))) :=
    of_eq (by simp only [T, allBody, allData_rename]) (HornBinderRules.under_body 2 hT U)
  exact allData_unique (HornBinderRules.zf_body 2 (HornBinderRules.zf_body 2 hZ T) U) R H
    (old 2 (old 2 w)) (old 2 (old 2 a)) (old 2 (old 2 A)) (old 2 (old 2 B)) (old 2 (old 2 C)) (old 2 (old 2 f)) (old 2 (old 2 j)) (old 2 (old 2 N)) (old 2 (old 2 Q)) (old 2 (old 2 V)) (fun i => old 2 (slot 2 i)) (slot 2) hw2 hx2 hU

/-- The exact four native binary cases, in original tag order 5/6/7/8. -/
def binary {n m} (kind : Fin 4) (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) : Formula m :=
  Fin.cases (andCode w a f N M Q)
    (Fin.cases (orCode R w a A f j N M Q)
      (Fin.cases (impCode R w a A f j N M Q) (fun _ => iffCode R w a A f j N M Q))) kind

theorem binary_rename {n m l} (kind : Fin 4) (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m) (r : Fin m → Fin l) :
    (binary kind R w a A f j N M Q).rename r = binary kind R (r w) (r a) (r A) (r f) (r j) (r N) (r M) (r Q) := by
  refine Fin.cases ?_ (fun i => ?_) kind
  · exact andCode_rename w a f N M Q r
  · refine Fin.cases ?_ (fun branchIndex => ?_) i
    · exact orCode_rename R w a A f j N M Q r
    · refine Fin.cases ?_ (fun _ => ?_) branchIndex
      · exact impCode_rename R w a A f j N M Q r
      · exact iffCode_rename R w a A f j N M Q r
def existsBinary {n m} (kind : Fin 4) (R : Source.Formula (n+2)) (w a A f j N M : Fin m) : Formula m := .ex
  (binary kind R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc M.castSucc (Fin.last m))

theorem binary_total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (R : Source.Formula (n+2))
    (w a A f j N M : Fin m) (hw : Derives Γ (omega w)) (hs : Derives Γ (successor A a))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j))
    (hn : Derives Γ (formulaCode w N a f)) (hm : Derives Γ (formulaCode w M a f)) : Derives Γ (existsBinary kind R w a A f j N M) := by
  refine Fin.cases ?_ (fun i => ?_) kind
  · exact and_total hZ w a f N M hw hn hm
  · refine Fin.cases ?_ (fun branchIndex => ?_) i
    · exact or_stage0 hZ R w a A f j N M ⟨hw,hs,hf,hj,hn,hm⟩
    · refine Fin.cases ?_ (fun _ => ?_) branchIndex
      · exact imp_stage0 hZ R w a A f j N M ⟨hw,hs,hf,hj,hn,hm⟩
      · exact iff_stage0 hZ R w a A f j N M ⟨hw,hs,hf,hj,hn,hm⟩
theorem binary_type {n m} {Γ : Context m} (kind : Fin 4) (R : Source.Formula (n+2)) (w a A f j N M Q : Fin m)
    (h : Derives Γ (binary kind R w a A f j N M Q)) : Derives Γ (formulaCode w Q a f) := by
  revert h
  refine Fin.cases ?_ (fun i => ?_) kind
  · intro h; exact and_type w a f N M Q h
  · refine Fin.cases ?_ (fun branchIndex => ?_) i
    · intro h; exact or_type R w a A f j N M Q h
    · refine Fin.cases ?_ (fun _ => ?_) branchIndex
      · intro h; exact imp_type R w a A f j N M Q h
      · intro h; exact iff_type R w a A f j N M Q h
theorem binary_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (R : Source.Formula (n+2))
    (w a A f j N M Q V : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (binary kind R w a A f j N M Q)) (hv : Derives Γ (binary kind R w a A f j N M V)) : Derives Γ (.equal Q V) := by
  revert hq hv
  refine Fin.cases ?_ (fun i => ?_) kind
  · intro hq hv; exact and_unique hZ w a f N M Q V hw hq hv
  · refine Fin.cases ?_ (fun branchIndex => ?_) i
    · intro hq hv; exact or_unique hZ R w a A f j N M Q V hw hq hv
    · refine Fin.cases ?_ (fun _ => ?_) branchIndex
      · intro hq hv; exact imp_unique hZ R w a A f j N M Q V hw hq hv
      · intro hq hv; exact iff_unique hZ R w a A f j N M Q V hw hq hv
/-- The native ALL case follows the pinned NEG/EX/NEG normalization. -/
def universal {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m) : Formula m :=
  allCode R H w a A B C f j N Q
theorem universal_rename {n m l} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m) (r : Fin m → Fin l) :
    (universal R H w a A B C f j N Q).rename r = universal R H (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) (r Q) :=
  allCode_rename R H w a A B C f j N Q r
def existsUniversal {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N : Fin m) : Formula m :=
  existsAll R H w a A B C f j N

theorem universal_total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2)) (H : Source.Formula (n+1))
    (w a A B C f j N : Fin m) (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j))
    (hn : Derives Γ (formulaCode w N A f)) : Derives Γ (existsUniversal R H w a A B C f j N) :=
  all_stage0 hZ R H w a A B C f j N ⟨hw,ha,hA,hB,hC,hf,hj,hn⟩
theorem universal_type {n m} {Γ : Context m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q : Fin m)
    (h : Derives Γ (universal R H w a A B C f j N Q)) : Derives Γ (formulaCode w Q a f) := all_type R H w a A B C f j N Q h
theorem universal_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2)) (H : Source.Formula (n+1))
    (w a A B C f j N Q V : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (universal R H w a A B C f j N Q)) (hv : Derives Γ (universal R H w a A B C f j N V)) : Derives Γ (.equal Q V) :=
  all_unique hZ R H w a A B C f j N Q V hw hq hv

def binarySentence {n m} (kind : Fin 4) (R : Source.Formula (n+2)) (w a A f j N M : Fin m) : Source.Sentence :=
  ((omega w).imp ((successor A a).imp ((SyntaxNumeralSyntax.numeral (n+2) f).imp ((SyntaxNumeralSyntax.numeral (n+1) j).imp ((formulaCode w N a f).imp ((formulaCode w M a f).imp (existsBinary kind R w a A f j N M))))))).close
theorem binary_kernel_certificate {n m} (kind : Fin 4) (R : Source.Formula (n+2)) (w a A f j N M : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (binarySentence kind R w a A f j N M)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact binary_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) _) kind R w a A f j N M
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
def binaryUniqueSentence {n m} (kind : Fin 4) (R : Source.Formula (n+2)) (w a A f j N M Q V : Fin m) : Source.Sentence :=
  ((omega w).imp ((binary kind R w a A f j N M Q).imp ((binary kind R w a A f j N M V).imp (Formula.equal Q V)))).close
theorem binary_unique_kernel_certificate {n m} (kind : Fin 4) (R : Source.Formula (n+2)) (w a A f j N M Q V : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (binaryUniqueSentence kind R w a A f j N M Q V)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact binary_unique (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) kind R w a A f j N M Q V (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

def universalSentence {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N : Fin m) : Source.Sentence :=
  ((omega w).imp ((Formula.mem a w).imp ((successor A a).imp ((successor B A).imp ((successor C B).imp ((SyntaxNumeralSyntax.numeral (n+2) f).imp ((SyntaxNumeralSyntax.numeral (n+1) j).imp ((formulaCode w N A f).imp (existsUniversal R H w a A B C f j N))))))))).close
theorem universal_kernel_certificate {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (universalSentence R H w a A B C f j N)) := by
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
  exact universal_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) _) _) _) R H w a A B C f j N
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
def universalUniqueSentence {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q V : Fin m) : Source.Sentence :=
  ((omega w).imp ((universal R H w a A B C f j N Q).imp ((universal R H w a A B C f j N V).imp (Formula.equal Q V)))).close
theorem universal_unique_kernel_certificate {n m} (R : Source.Formula (n+2)) (H : Source.Formula (n+1)) (w a A B C f j N Q V : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (universalUniqueSentence R H w a A B C f j N Q V)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact universal_unique (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) R H w a A B C f j N Q V (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingLogicalCode