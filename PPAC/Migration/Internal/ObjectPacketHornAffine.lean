import PPAC.Migration.Internal.PacketHornAffineLaws

/-! Original Packet affine expression and complete local rule matrix correspondence; global Horn condition and byte bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketHornAffine
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetOriginalAddConstGraphIffSentence {m} (k n : Nat) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w x B y : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat n w env).imp ((HornExprSyntax.graph e w env x).imp ((SyntaxNumeralSyntax.numeral k B).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectPacket.Expr.addConst k e) w env y).iff (NaturalAdditionSyntax.sum w x B y))))))).close

theorem source_packetOriginalAddConstGraphIff {m} (k n : Nat) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w x B y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetOriginalAddConstGraphIffSentence k n e env w x B y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral k B) (Context.add (HornExprSyntax.graph e w env x) (Context.add (HornExprSyntax.environmentNat n w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat n w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph e w env x) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral k B) := .hyp (Or.inl rfl)
  exact HornExprAddConst.graph_iff hZ k e w x B y env h0 h1 h2 h3

theorem packetOriginalAddConstGraphIff_kernel_certificate {m} (k n : Nat) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w x B y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetOriginalAddConstGraphIffSentence k n e env w x B y)) := TheoryTransport.sentence (source_packetOriginalAddConstGraphIff k n e env w x B y)

theorem native_packetOriginalAddConstGraphIff {m} (k n : Nat) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w x B y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetOriginalAddConstGraphIffSentence k n e env w x B y)) := ZFReplay.replay (packetOriginalAddConstGraphIff_kernel_certificate k n e env w x B y)

def packetOriginalRadixAddConstGraphIffSentence {m} (wide : Bool) (env : Fin 3 → Fin m) (w B y : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectPacket.Expr.addConst (PacketAffineRuleData.radix wide) (.var 2)) w env y).iff (NaturalAdditionSyntax.sum w (env 2) B y)))))).close

theorem source_packetOriginalRadixAddConstGraphIff {m} (wide : Bool) (env : Fin 3 → Fin m) (w B y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetOriginalRadixAddConstGraphIffSentence wide env w B y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inl rfl)
  exact HornExprAddConst.graph_iff hZ (PacketAffineRuleData.radix wide) (.var 2) w (env 2) B y env h0 h1 (.conjI (HornExprSyntax.environmentNat_at w env h1 2) (.eqRefl _)) h2

theorem packetOriginalRadixAddConstGraphIff_kernel_certificate {m} (wide : Bool) (env : Fin 3 → Fin m) (w B y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetOriginalRadixAddConstGraphIffSentence wide env w B y)) := TheoryTransport.sentence (source_packetOriginalRadixAddConstGraphIff wide env w B y)

theorem native_packetOriginalRadixAddConstGraphIff {m} (wide : Bool) (env : Fin 3 → Fin m) (w B y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetOriginalRadixAddConstGraphIffSentence wide env w B y)) := ZFReplay.replay (packetOriginalRadixAddConstGraphIff_kernel_certificate wide env w B y)

def packetOriginalAffineBaseHeadIffSentence {m} (wide : Bool) (env : Fin 1 → Fin m) (w z r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 1 w env).imp ((empty z).imp (((HornExprSyntax.graph (PacketAffineRuleData.baseRule wide).head w env r).iff (PacketHornAffineSyntax.row wide w (env 0) z (env 0) r)))))).close

theorem source_packetOriginalAffineBaseHeadIff {m} (wide : Bool) (env : Fin 1 → Fin m) (w z r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetOriginalAffineBaseHeadIffSentence wide env w z r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 1 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 1 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact PacketHornAffineExpr.base_head_iff hZ wide w z r env h0 h1 h2

theorem packetOriginalAffineBaseHeadIff_kernel_certificate {m} (wide : Bool) (env : Fin 1 → Fin m) (w z r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetOriginalAffineBaseHeadIffSentence wide env w z r)) := TheoryTransport.sentence (source_packetOriginalAffineBaseHeadIff wide env w z r)

theorem native_packetOriginalAffineBaseHeadIff {m} (wide : Bool) (env : Fin 1 → Fin m) (w z r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetOriginalAffineBaseHeadIffSentence wide env w z r)) := ZFReplay.replay (packetOriginalAffineBaseHeadIff_kernel_certificate wide env w z r)

def packetOriginalAffineStepHeadIffSentence {m} (wide : Bool) (env : Fin 3 → Fin m) (w B s y r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((successor s (env 1)).imp ((NaturalAdditionSyntax.sum w (env 2) B y).imp (((HornExprSyntax.graph (PacketAffineRuleData.stepRule wide).head w env r).iff (PacketHornAffineSyntax.row wide w (env 0) s y r)))))))).close

theorem source_packetOriginalAffineStepHeadIff {m} (wide : Bool) (env : Fin 3 → Fin m) (w B s y r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetOriginalAffineStepHeadIffSentence wide env w B s y r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalAdditionSyntax.sum w (env 2) B y) (Context.add (successor s (env 1)) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor s (env 1)) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (NaturalAdditionSyntax.sum w (env 2) B y) := .hyp (Or.inl rfl)
  exact PacketHornAffineExpr.step_head_iff hZ wide w B s y r env h0 h1 h2 h3 h4

theorem packetOriginalAffineStepHeadIff_kernel_certificate {m} (wide : Bool) (env : Fin 3 → Fin m) (w B s y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetOriginalAffineStepHeadIffSentence wide env w B s y r)) := TheoryTransport.sentence (source_packetOriginalAffineStepHeadIff wide env w B s y r)

theorem native_packetOriginalAffineStepHeadIff {m} (wide : Bool) (env : Fin 3 → Fin m) (w B s y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetOriginalAffineStepHeadIffSentence wide env w B s y r)) := ZFReplay.replay (packetOriginalAffineStepHeadIff_kernel_certificate wide env w B s y r)

def packetOriginalAffineBaseGuardIffSentence {m} (wide : Bool) (env : Fin 1 → Fin m) (w B : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 1 w env).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp (((HornRuleSyntax.guard (.var 0) (.literal (PacketAffineRuleData.radix wide)) w env).iff (Formula.mem (env 0) B)))))).close

theorem source_packetOriginalAffineBaseGuardIff {m} (wide : Bool) (env : Fin 1 → Fin m) (w B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetOriginalAffineBaseGuardIffSentence wide env w B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (HornExprSyntax.environmentNat 1 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 1 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inl rfl)
  exact PacketHornAffineExpr.base_guard_iff hZ wide w B env h0 h1 h2

theorem packetOriginalAffineBaseGuardIff_kernel_certificate {m} (wide : Bool) (env : Fin 1 → Fin m) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetOriginalAffineBaseGuardIffSentence wide env w B)) := TheoryTransport.sentence (source_packetOriginalAffineBaseGuardIff wide env w B)

theorem native_packetOriginalAffineBaseGuardIff {m} (wide : Bool) (env : Fin 1 → Fin m) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetOriginalAffineBaseGuardIffSentence wide env w B)) := ZFReplay.replay (packetOriginalAffineBaseGuardIff_kernel_certificate wide env w B)

def packetOriginalAffineStepPremiseIffSentence {m} (wide : Bool) (env : Fin 3 → Fin m) (w V : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornRuleSyntax.premise (YesMetaZFC.Automation.ObjectPacket.node (PacketAffineRuleData.relation wide) [.var 0,.var 1,.var 2]) w V env).iff (PacketHornAffineSyntax.entry wide w V (env 0) (env 1) (env 2)))))).close

theorem source_packetOriginalAffineStepPremiseIff {m} (wide : Bool) (env : Fin 3 → Fin m) (w V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetOriginalAffineStepPremiseIffSentence wide env w V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact PacketHornAffineExpr.step_premise_iff hZ wide w V env h0 h1

theorem packetOriginalAffineStepPremiseIff_kernel_certificate {m} (wide : Bool) (env : Fin 3 → Fin m) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetOriginalAffineStepPremiseIffSentence wide env w V)) := TheoryTransport.sentence (source_packetOriginalAffineStepPremiseIff wide env w V)

theorem native_packetOriginalAffineStepPremiseIff {m} (wide : Bool) (env : Fin 3 → Fin m) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetOriginalAffineStepPremiseIffSentence wide env w V)) := ZFReplay.replay (packetOriginalAffineStepPremiseIff_kernel_certificate wide env w V)

def packetOriginalAffineBaseMatrixAtIffSentence {m} (wide : Bool) (env : Fin 1 → Fin m) (w B z r V : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 1 w env).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((empty z).imp (((HornRuleSyntax.matrix (PacketAffineRuleData.baseRule wide) w r V env).iff ((PacketHornAffineSyntax.row wide w (env 0) z (env 0) r).conj (Formula.mem (env 0) B)))))))).close

theorem source_packetOriginalAffineBaseMatrixAtIff {m} (wide : Bool) (env : Fin 1 → Fin m) (w B z r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetOriginalAffineBaseMatrixAtIffSentence wide env w B z r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (HornExprSyntax.environmentNat 1 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 1 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact PacketHornAffineMatrix.base_at hZ wide w B z r V env h0 h1 h2 h3

theorem packetOriginalAffineBaseMatrixAtIff_kernel_certificate {m} (wide : Bool) (env : Fin 1 → Fin m) (w B z r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetOriginalAffineBaseMatrixAtIffSentence wide env w B z r V)) := TheoryTransport.sentence (source_packetOriginalAffineBaseMatrixAtIff wide env w B z r V)

theorem native_packetOriginalAffineBaseMatrixAtIff {m} (wide : Bool) (env : Fin 1 → Fin m) (w B z r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetOriginalAffineBaseMatrixAtIffSentence wide env w B z r V)) := ZFReplay.replay (packetOriginalAffineBaseMatrixAtIff_kernel_certificate wide env w B z r V)

def packetOriginalAffineStepMatrixAtIffSentence {m} (wide : Bool) (env : Fin 3 → Fin m) (w B s y r V : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((successor s (env 1)).imp ((NaturalAdditionSyntax.sum w (env 2) B y).imp (((HornRuleSyntax.matrix (PacketAffineRuleData.stepRule wide) w r V env).iff ((PacketHornAffineSyntax.row wide w (env 0) s y r).conj (PacketHornAffineSyntax.entry wide w V (env 0) (env 1) (env 2)))))))))).close

theorem source_packetOriginalAffineStepMatrixAtIff {m} (wide : Bool) (env : Fin 3 → Fin m) (w B s y r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetOriginalAffineStepMatrixAtIffSentence wide env w B s y r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalAdditionSyntax.sum w (env 2) B y) (Context.add (successor s (env 1)) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor s (env 1)) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (NaturalAdditionSyntax.sum w (env 2) B y) := .hyp (Or.inl rfl)
  exact PacketHornAffineMatrix.step_at hZ wide w B s y r V env h0 h1 h2 h3 h4

theorem packetOriginalAffineStepMatrixAtIff_kernel_certificate {m} (wide : Bool) (env : Fin 3 → Fin m) (w B s y r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetOriginalAffineStepMatrixAtIffSentence wide env w B s y r V)) := TheoryTransport.sentence (source_packetOriginalAffineStepMatrixAtIff wide env w B s y r V)

theorem native_packetOriginalAffineStepMatrixAtIff {m} (wide : Bool) (env : Fin 3 → Fin m) (w B s y r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetOriginalAffineStepMatrixAtIffSentence wide env w B s y r V)) := ZFReplay.replay (packetOriginalAffineStepMatrixAtIff_kernel_certificate wide env w B s y r V)

def packetOriginalAffineBaseMatrixIffSentence {m} (wide : Bool) (env : Fin 1 → Fin m) (w B r V : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 1 w env).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp (((HornRuleSyntax.matrix (PacketAffineRuleData.baseRule wide) w r V env).iff (PacketHornAffineSyntax.base wide w B (env 0) r)))))).close

theorem source_packetOriginalAffineBaseMatrixIff {m} (wide : Bool) (env : Fin 1 → Fin m) (w B r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetOriginalAffineBaseMatrixIffSentence wide env w B r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (HornExprSyntax.environmentNat 1 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 1 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inl rfl)
  exact PacketHornAffineLocal.base_iff hZ wide w B r V env h0 h1 h2

theorem packetOriginalAffineBaseMatrixIff_kernel_certificate {m} (wide : Bool) (env : Fin 1 → Fin m) (w B r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetOriginalAffineBaseMatrixIffSentence wide env w B r V)) := TheoryTransport.sentence (source_packetOriginalAffineBaseMatrixIff wide env w B r V)

theorem native_packetOriginalAffineBaseMatrixIff {m} (wide : Bool) (env : Fin 1 → Fin m) (w B r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetOriginalAffineBaseMatrixIffSentence wide env w B r V)) := ZFReplay.replay (packetOriginalAffineBaseMatrixIff_kernel_certificate wide env w B r V)

def packetOriginalAffineStepMatrixIffSentence {m} (wide : Bool) (env : Fin 3 → Fin m) (w B r V : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp (((HornRuleSyntax.matrix (PacketAffineRuleData.stepRule wide) w r V env).iff (PacketHornAffineSyntax.step wide w B V (env 0) (env 1) (env 2) r)))))).close

theorem source_packetOriginalAffineStepMatrixIff {m} (wide : Bool) (env : Fin 3 → Fin m) (w B r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetOriginalAffineStepMatrixIffSentence wide env w B r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inl rfl)
  exact PacketHornAffineLocal.step_iff hZ wide w B r V env h0 h1 h2

theorem packetOriginalAffineStepMatrixIff_kernel_certificate {m} (wide : Bool) (env : Fin 3 → Fin m) (w B r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetOriginalAffineStepMatrixIffSentence wide env w B r V)) := TheoryTransport.sentence (source_packetOriginalAffineStepMatrixIff wide env w B r V)

theorem native_packetOriginalAffineStepMatrixIff {m} (wide : Bool) (env : Fin 3 → Fin m) (w B r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetOriginalAffineStepMatrixIffSentence wide env w B r V)) := ZFReplay.replay (packetOriginalAffineStepMatrixIff_kernel_certificate wide env w B r V)

def packetOriginalAffineAllInternalBaseMatrixLawSentence {m} (wide : Bool) (w B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketHornAffineLawSyntax.baseLaw wide w B)))).close

theorem source_packetOriginalAffineAllInternalBaseMatrixLaw {m} (wide : Bool) (w B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetOriginalAffineAllInternalBaseMatrixLawSentence wide w B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inl rfl)
  exact PacketHornAffineLaws.base_law hZ wide w B h0 h1

theorem packetOriginalAffineAllInternalBaseMatrixLaw_kernel_certificate {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetOriginalAffineAllInternalBaseMatrixLawSentence wide w B)) := TheoryTransport.sentence (source_packetOriginalAffineAllInternalBaseMatrixLaw wide w B)

theorem native_packetOriginalAffineAllInternalBaseMatrixLaw {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetOriginalAffineAllInternalBaseMatrixLawSentence wide w B)) := ZFReplay.replay (packetOriginalAffineAllInternalBaseMatrixLaw_kernel_certificate wide w B)

def packetOriginalAffineAllInternalStepMatrixLawSentence {m} (wide : Bool) (w B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketHornAffineLawSyntax.stepLaw wide w B)))).close

theorem source_packetOriginalAffineAllInternalStepMatrixLaw {m} (wide : Bool) (w B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetOriginalAffineAllInternalStepMatrixLawSentence wide w B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inl rfl)
  exact PacketHornAffineLaws.step_law hZ wide w B h0 h1

theorem packetOriginalAffineAllInternalStepMatrixLaw_kernel_certificate {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetOriginalAffineAllInternalStepMatrixLawSentence wide w B)) := TheoryTransport.sentence (source_packetOriginalAffineAllInternalStepMatrixLaw wide w B)

theorem native_packetOriginalAffineAllInternalStepMatrixLaw {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetOriginalAffineAllInternalStepMatrixLawSentence wide w B)) := ZFReplay.replay (packetOriginalAffineAllInternalStepMatrixLaw_kernel_certificate wide w B)

def packetOriginalAffineLiteralMatrixSystemExistsSentence {m} (wide : Bool) (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketHornAffineLawSyntax.existsSystem wide w))).close

theorem source_packetOriginalAffineLiteralMatrixSystemExists {m} (wide : Bool) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetOriginalAffineLiteralMatrixSystemExistsSentence wide w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketHornAffineLaws.exists_system hZ wide w h0

theorem packetOriginalAffineLiteralMatrixSystemExists_kernel_certificate {m} (wide : Bool) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetOriginalAffineLiteralMatrixSystemExistsSentence wide w)) := TheoryTransport.sentence (source_packetOriginalAffineLiteralMatrixSystemExists wide w)

theorem native_packetOriginalAffineLiteralMatrixSystemExists {m} (wide : Bool) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetOriginalAffineLiteralMatrixSystemExistsSentence wide w)) := ZFReplay.replay (packetOriginalAffineLiteralMatrixSystemExists_kernel_certificate wide w)

end PPAC.Migration.Internal.ObjectPacketHornAffine
