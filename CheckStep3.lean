import PPAC

/-! 反向句法的对象核回放；不宣称Replacement/Collection或两种AC已等价。 -/
namespace PPAC.Migration.Step3Checks
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature
abbrev noAxioms : FirstOrder.Theory ℒ := fun _ => False

def binders : FirstOrder.Sentence ℒ :=
  .forallE .set (.existsE .set (.neg
    (.rel .membership (.cons (.bvar (.there .here)) (.cons (.bvar .here) .nil)))))

/-- 原生首变量绑定严格变成源末变量绑定。 -/
example : Reverse.sentence binders = .all (.ex ((Source.Formula.mem 0 1).neg)) := rfl

/-- 原生独立连接词展开成源8构造器，无真值谓词或新符号。 -/
example : Reverse.sentence (.iff .truth (.neg .falsum)) =
    (Source.Formula.imp .bot .bot).iff (.imp .bot .bot) := rfl

/-- 嵌套混合量词的等价是实际对象推导，而不是Realize定理。 -/
theorem binder_roundtrip : FirstOrder.Derives noAxioms []
    (.iff binders (Translation.sentence (Reverse.sentence binders))) :=
  Reverse.sentence_equivalent binders

def allConnectives : FirstOrder.Sentence ℒ :=
  .conj (.iff .truth (.imp .falsum .falsum))
    (.forallE .set (.disj (.equal (.bvar .here) (.bvar .here))
      (.existsE .set (.neg (.equal (.bvar .here) (.bvar (.there .here)))))))

theorem all_connectives_roundtrip : FirstOrder.Derives noAxioms []
    (.iff allConnectives (Translation.sentence (Reverse.sentence allConnectives))) :=
  Reverse.sentence_equivalent allConnectives

example : Reverse.sentence (Translation.sentence Source.SetLanguage.PP) = Source.SetLanguage.PP :=
  Reverse.source_sentence_roundtrip _
example : Reverse.sentence (Translation.sentence Source.SetLanguage.AC) = Source.SetLanguage.AC :=
  Reverse.source_sentence_roundtrip _
example : Reverse.sentence (Translation.sentence Source.SetLanguage.ACwo) = Source.SetLanguage.ACwo :=
  Reverse.source_sentence_roundtrip _

/-- 任意参数个数和任意矩阵，非有限样本。 -/
theorem replacement_roundtrip {n} (p : Source.Formula (n+2)) :
    Reverse.sentence (Translation.sentence (Source.SetLanguage.replacement p)) =
      Source.SetLanguage.replacement p := Reverse.source_sentence_roundtrip _

theorem separation_roundtrip {n} (p : Source.Formula (n+1)) :
    Reverse.sentence (Translation.sentence (Source.SetLanguage.separation p)) =
      Source.SetLanguage.separation p := Reverse.source_sentence_roundtrip _

/-- 任意理论和开放推导均可在规范化公理呈现间回放。 -/
theorem presentation_replay {T : FirstOrder.Theory ℒ} {free : Syntax.Ctx}
    {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free}
    (h : FirstOrder.Derives T Γ p) :
    FirstOrder.Derives (Presentation.theory T) Γ p := Presentation.derives_iff.mpr h

theorem native_ZF_presentation {free : Syntax.Ctx}
    {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free} :
    FirstOrder.Derives (Presentation.theory nativeZF) Γ p ↔
      FirstOrder.Derives nativeZF Γ p := Presentation.derives_iff

/-- 原生外延公理的规范化确实落在source语法像；不等同于源ZF呈现等价。 -/
theorem native_extensionality_replay :
    FirstOrder.Derives (Presentation.theory nativeZF) []
      (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.extensionality) := by
  apply Presentation.replay_original_axiom
  exact ⟨_, SetTheory.ZF.Axiom.extensionality, rfl⟩

/-- 五条已对齐公理，验收源→原生、原生→源句子像两个方向。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.extensionality) :=
  ZFEquivalence.source_extensionality
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.emptySet) :=
  ZFEquivalence.source_emptySet
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.pairing) :=
  ZFEquivalence.source_pairing
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.union) :=
  ZFEquivalence.source_union
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.powerSet) :=
  ZFEquivalence.source_powerSet
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.extensionality) := ZFEquivalence.native_extensionality
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.emptySet) := ZFEquivalence.native_emptySet
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.pairing) := ZFEquivalence.native_pairing
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.union) := ZFEquivalence.native_union
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.powerSet) := ZFEquivalence.native_powerSet
/-- 七条固定公理已经双向覆盖；新增两条均为对象原核推导。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.infinity) := ZFEquivalence.source_infinity
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.foundation) := ZFEquivalence.source_foundation
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.infinity) := ZFEquivalence.native_infinity
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.foundation) := ZFEquivalence.native_foundation

/-- 全分离模式，不限制参数个数和矩阵复杂度。 -/
theorem separation_source_to_native {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (Source.SetLanguage.separation p)) :=
  SeparationSyntax.source_separation p

theorem separation_native_of_source_matrix {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives ZFEquivalence.sourceZF []
      (SetTheory.Definitional.Project.fo_sentence
        (SetTheory.Axioms.Schema.separation (ProjectSyntax.unary p))) :=
  SeparationSyntax.native_separation_of_source_matrix p

/-- 多个参数和内嵌混合量词的实例也走同一个全模式定理。 -/
def parameterMatrix : Source.Formula 4 :=
  .all (.ex ((Source.Formula.mem 5 0).conj ((Source.Formula.mem 4 3).imp (.equal 1 2))))
example : FirstOrder.Derives nativeZF []
    (Translation.sentence (Source.SetLanguage.separation parameterMatrix)) :=
  SeparationSyntax.source_separation parameterMatrix
/-- 任意原生矩阵的反向分离模式，不再只限于ProjectSyntax.unary p。 -/
theorem arbitrary_native_separation {n} (s : SetTheory.Definitional.Project.UnarySchema n) :
    FirstOrder.Derives ZFEquivalence.sourceZF []
      (SetTheory.Definitional.Project.fo_sentence (SetTheory.Axioms.Schema.separation s)) :=
  SeparationReverse.native_separation s

def projectMatrix : SetTheory.Definitional.Project.UnarySchema 2 where
  body := .iff .truth (.forallE (.imp
    (SetTheory.Definitional.Project.Formula.subset (.bound 0) (.bound 1))
    (.neg (SetTheory.Definitional.Project.Formula.extensionalEq (.bound 2) (.bound 3)))))
  freeClosed := by simp [SetTheory.Definitional.Formula.FreeClosed]

/-- 子集原子、独立连接词、多个参数和量词同时出现的实际原核回放。 -/
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence (SetTheory.Axioms.Schema.separation projectMatrix)) :=
  SeparationReverse.native_separation projectMatrix

/-- 全参数Collection的源呈现只从原Collection版ZF取得，没有假定源ZF已经证明它。 -/
theorem collection_source_presentation {n} (p : Source.Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (CollectionSyntax.collection p)) :=
  CollectionSyntax.source_collection p

theorem arbitrary_collection_roundtrip {n} (s : SetTheory.Definitional.Project.BinarySchema n) :
    FirstOrder.Derives noAxioms [] (.iff
      (SetTheory.Definitional.Project.fo_sentence (SetTheory.Axioms.Schema.collection s))
      (Translation.sentence (CollectionSyntax.collection (ProjectDecode.reverse s.body s.freeClosed)))) :=
  CollectionSyntax.native_collection_equivalent s
/-- 任意参数及任意矩阵的原始Replacement句子，实际在原Collection版ZF内推导。 -/
theorem all_source_replacement {n} (p : Source.Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (Source.SetLanguage.replacement p)) :=
  ReplacementFromCollection.native_replacement p

/-- 两模式实例的原核证书与原ZF回放分开验收，防止循环假定Replacement。 -/
theorem replacement_two_instances {n} (p : Source.Formula (n+2)) :
    FirstOrder.Derives (TheoryTransport.theory (ReplacementFromCollection.assumptions p)) []
      (Translation.sentence (Source.SetLanguage.replacement p)) :=
  ReplacementFromCollection.kernel_certificate p

theorem source_ZF_full_replay {n} {p : Source.Sentence}
    (h : Source.Derives (Source.SetLanguage.ZF.at n) (p.rename Fin.elim0)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence p) := ZFReplay.source_closed_at h

theorem source_target_full_replay {n} {p : Source.Sentence}
    (h : Source.Derives (Source.SetLanguage.targetTheory.at n) (p.rename Fin.elim0)) :
    FirstOrder.Derives targetTheory [] (Translation.sentence p) := ZFReplay.source_target_closed_at h

/-- 实际源Replacement公理证书经完整源ZF接口回放；不再停留在未对应的理论像。 -/
theorem replay_replacement_through_source_ZF {n} (p : Source.Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (Source.SetLanguage.replacement p)) := by
  apply ZFReplay.source_closed_at (n := 1)
  exact .hyp ⟨_, Source.SetLanguage.IsZFAxiom.replacement p, rfl⟩

example : FirstOrder.Derives nativeZF []
    (Translation.sentence (Source.SetLanguage.replacement (Source.Formula.equal 0 1 : Source.Formula 2))) :=
  ReplacementFromCollection.native_replacement _

example : FirstOrder.Derives nativeZF []
    (Translation.sentence (Source.SetLanguage.replacement
      (Source.Formula.all (.ex ((Source.Formula.mem 5 0).conj ((Source.Formula.mem 3 4).imp (.equal 1 2)))) : Source.Formula 4))) :=
  ReplacementFromCollection.native_replacement _
/-- 六规则总接口，包括任意开放结论、局部假设和非单射变量编号。 -/
theorem native_open_reverse {T : FirstOrder.Theory ℒ} {free : Syntax.Ctx}
    {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free}
    (d : FirstOrder.Derives T Γ p) {n} (default : Fin n) (f : Reverse.Vars free n) :
    Source.Derives (ReverseCompile.context T f Γ) (Reverse.formula ReverseSubstitution.empty f p) :=
  ReverseCompile.derives d default f

theorem every_native_logical_mode {free : Syntax.Ctx} {p : Syntax.Fm [] free}
    (h : HilbertBaseAxiom ℒ p) {n} {Γ : Source.Context n} (f : Reverse.Vars free n) :
    Source.Derives Γ (Reverse.formula ReverseSubstitution.empty f p) :=
  ReverseLogicalAxioms.replay h f

/-- 无函数常元的纯语言：存在对象由原核强化规则证明，回译不能假定Fin 0有变量。 -/
def inhabited : FirstOrder.Sentence ℒ := .existsE .set (.equal (.bvar .here) (.bvar .here))

def inhabitedCertificate : HilbertDerivation noAxioms [] inhabited := by
  apply HilbertDerivation.free_strengthening (sort := SetSort.set)
  change HilbertDerivation noAxioms [SetSort.set]
    (.existsE SetSort.set (.equal (.bvar .here) (.bvar .here)))
  exact .modus_ponens (.logical_axiom (.equality_reflexivity (.fvar .here)))
    (.logical_axiom (.exists_introduction (σ := ℒ) (free := [SetSort.set]) SetSort.set (.equal (.bvar .here) (.bvar .here)) (.fvar .here)))

example : Source.Derives ((Presentation.source noAxioms).at 1)
    ((Reverse.sentence inhabited).rename Fin.elim0) :=
  ReverseCompile.sentence ⟨inhabitedCertificate⟩

/-- 直接在源空理论的一个变量环境证明确切回译句，没有非空公理。 -/
example : Source.Derives (Source.Theory.at (fun _ : Source.Sentence => False) 1)
    ((Reverse.sentence inhabited).rename Fin.elim0) := by
  have h := ReverseCompile.sentence ⟨inhabitedCertificate⟩
  apply Source.Derives.weaken _ h
  rintro q ⟨_, ⟨_, hfalse, _⟩, _⟩
  exact False.elim hfalse

theorem arbitrary_source_sentence_roundtrip {T : Source.Theory} {p : Source.Sentence} :
    FirstOrder.Derives (TheoryTransport.theory T) [] (Translation.sentence p) ↔
      Source.Derives (T.at 1) (p.rename Fin.elim0) :=
  ReverseCompile.source_sentence_iff
/-- 极小元与有界归纳均返回原核Derives，矩阵和参数数目完全任意。 -/
theorem full_bounded_minimal_schema {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (BoundedMinimal.sentence p)) :=
  BoundedMinimal.native_minimal p

theorem full_bounded_induction_schema {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (BoundedInduction.sentence p)) :=
  BoundedInduction.native_induction p

/-- 源Replacement版ZF端亦有证书，本引理没有使用源Collection。 -/
theorem source_bounded_induction_without_collection {n} (p : Source.Formula (n+1)) :
    Source.Derives (Source.SetLanguage.ZF.at 0) (BoundedInduction.sentence p) :=
  BoundedInduction.source_ZF_induction p

/-- 一个分离实例与Foundation足够，和原生ZF句子闭合可信基分开验收。 -/
theorem bounded_minimal_two_instances {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives (TheoryTransport.theory (BoundedMinimal.assumptions p)) []
      (Translation.sentence (BoundedMinimal.sentence p)) :=
  BoundedMinimal.kernel_certificate p

theorem bounded_induction_two_instances {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives (TheoryTransport.theory (BoundedMinimal.assumptions p.neg)) []
      (Translation.sentence (BoundedInduction.sentence p)) :=
  BoundedInduction.kernel_certificate p

example : FirstOrder.Derives nativeZF [] (Translation.sentence (BoundedMinimal.sentence parameterMatrix)) :=
  BoundedMinimal.native_minimal parameterMatrix

example : FirstOrder.Derives nativeZF [] (Translation.sentence (BoundedInduction.sentence parameterMatrix)) :=
  BoundedInduction.native_induction parameterMatrix
/-- 全部对象x/y都有唯一Kuratowski编码，输出实际原核闭句。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectPairs.existenceSentence) :=
  ObjectPairs.native_exists_unique

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectPairs.characterizationSentence) :=
  ObjectPairs.native_characterization

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectPairs.existenceSentence :=
  ObjectPairs.source_ZF_exists_unique

example : FirstOrder.Derives (TheoryTransport.theory ObjectPairs.assumptions) []
    (Translation.sentence ObjectPairs.characterizationSentence) := ObjectPairs.characterization_kernel_certificate

/-- 编码严格使用源PP/AC中同一个orderedPair定义。 -/
example {n} (p x y : Fin n) : Source.SetLanguage.orderedPair p x y = PairSyntax.ordered p x y :=
  PairSyntax.ordered_original p x y

/-- 对象x=y也覆盖：同一个变量槽的实际全称闭句，不以分量不同为前提。 -/
def diagonalOrderedPair : Source.Sentence := (ObjectPairs.existsUnique (0 : Fin 1) 0).close

theorem diagonal_ordered_pair : FirstOrder.Derives nativeZF [] (Translation.sentence diagonalOrderedPair) := by
  apply ObjectPairs.native_replay
  apply TheoryTransport.sentence
  apply SourceAlgebra.close_derives
  exact ObjectPairs.exists_unique 0 0 (.hyp ⟨_, Or.inl rfl, rfl⟩) (.hyp ⟨_, Or.inr rfl, rfl⟩)

/-- 任意非单射变量编号及任意局部假设的完整开放分量刻画。 -/
theorem arbitrary_ordered_pair_characterization {n} {Γ : Source.Context n} (p q x y a b : Fin n)
    (he : Source.Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hp : Source.Derives Γ (PairSyntax.ordered p x y)) (hq : Source.Derives Γ (PairSyntax.ordered q a b)) :
    Source.Derives Γ ((Source.Formula.equal p q).iff ((Source.Formula.equal x a).conj (.equal y b))) :=
  OrderedPairLogic.characterization p q x y a b he hp hq
/-- 源edge/functionOn的完整AST严格保留，未删去无杂项或精确定义域条件。 -/
example {n} (f x y : Fin n) : Source.SetLanguage.edge f x y = GraphSyntax.edge f x y :=
  GraphSyntax.edge_original f x y

example {n} (f d : Fin n) : Source.SetLanguage.functionOn f d = GraphSyntax.functionOn f d :=
  GraphSyntax.functionOn_original f d

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphs.singletonSentence) := ObjectGraphs.native_singleton
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphs.evaluationSentence) := ObjectGraphs.native_evaluation
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphs.domainSentence) := ObjectGraphs.native_domain
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphs.singleValuedSentence) := ObjectGraphs.native_single_valued

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectGraphs.singletonSentence := ObjectGraphs.source_ZF_singleton
example : FirstOrder.Derives (TheoryTransport.theory ObjectGraphs.assumptions) []
    (Translation.sentence ObjectGraphs.singletonSentence) := ObjectGraphs.singleton_kernel_certificate

/-- 开放接口直接证明源原functionOn，包括定义域/图的所有原量词。 -/
theorem singleton_is_original_function {n} {Γ : Source.Context n} (f p d x y : Fin n)
    (he : Source.Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Source.Derives Γ (PairSyntax.pair f p p)) (hp : Source.Derives Γ (PairSyntax.ordered p x y))
    (hd : Source.Derives Γ (PairSyntax.pair d x x)) : Source.Derives Γ (Source.SetLanguage.functionOn f d) := by
  rw [GraphSyntax.functionOn_original]
  exact SingletonGraphLogic.function_on_singleton f p d x y he hf hp hd

/-- 重复输入/输出槽也走同一原核证书；不存在暗加的不同性前提。 -/
def diagonalSingletonMap : Source.Sentence := (SingletonMap.existsMap (0 : Fin 1) 0).close

theorem diagonal_singleton_map : FirstOrder.Derives nativeZF [] (Translation.sentence diagonalSingletonMap) := by
  apply ObjectPairs.native_replay
  apply TheoryTransport.sentence
  apply SourceAlgebra.close_derives
  exact SingletonMap.exists_map 0 0 (.hyp ⟨_, Or.inl rfl, rfl⟩) (.hyp ⟨_, Or.inr rfl, rfl⟩)
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphs.totalSentence) := ObjectGraphs.native_total
/-- 实际集合插入、原successor、一般新点图扩展及全部边刻画。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphInsert.insertSentence) := ObjectGraphInsert.native_insert
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphInsert.successorSentence) := ObjectGraphInsert.native_successor
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphInsert.extensionSentence) := ObjectGraphInsert.native_extension
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphInsert.edgeLawSentence) := ObjectGraphInsert.native_edge_law

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectGraphInsert.extensionSentence := ObjectGraphInsert.source_ZF_extension
example : FirstOrder.Derives (TheoryTransport.theory ObjectGraphInsert.assumptions) []
    (Translation.sentence ObjectGraphInsert.extensionSentence) := ObjectGraphInsert.extension_kernel_certificate

example {n} (b a : Fin n) : Source.SetLanguage.successor b a = InsertSyntax.insert b a a := InsertSyntax.successor_original b a

/-- 开放扩展结论仍是完整源functionOn，而不是只保留边的单值性。 -/
theorem extension_is_original_function {n} {Γ : Source.Context n} (g e f d p x y : Fin n)
    (he : Source.Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Source.Derives Γ (Source.SetLanguage.functionOn f d)) (hn : Source.Derives Γ (Source.Formula.mem x d).neg)
    (hg : Source.Derives Γ (InsertSyntax.insert g f p)) (hd : Source.Derives Γ (InsertSyntax.insert e d x))
    (hp : Source.Derives Γ (PairSyntax.ordered p x y)) : Source.Derives Γ (Source.SetLanguage.functionOn g e) := by
  rw [GraphSyntax.functionOn_original] at hf ⊢
  exact GraphInsertFunction.function_insert g e f d p x y he hf hn hg hd hp

/-- 新点的输出可等于输入；原前提仅为输入不在旧域。 -/
def diagonalGraphExtension : Source.Sentence :=
  ((GraphSyntax.functionOn (0 : Fin 3) 1).imp ((Source.Formula.mem 2 1).neg.imp
    (GraphInsertSyntax.existsExtension 0 1 2 2))).close

theorem diagonal_graph_extension : FirstOrder.Derives nativeZF [] (Translation.sentence diagonalGraphExtension) := by
  apply ObjectGraphInsert.native_replay
  apply TheoryTransport.sentence
  apply SourceAlgebra.close_derives
  apply Source.Derives.impI
  apply Source.Derives.impI
  have hp : Source.Derives (ObjectGraphInsert.assumptions.at 3) (Source.SetLanguage.pairing.rename Fin.elim0) :=
    .hyp ⟨_, Or.inl rfl, rfl⟩
  have hu : Source.Derives (ObjectGraphInsert.assumptions.at 3) (Source.SetLanguage.union.rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩
  have he : Source.Derives (ObjectGraphInsert.assumptions.at 3) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inr rfl), rfl⟩
  exact GraphInsertExistence.exists_extension 0 1 2 2 (SourceLogic.add (SourceLogic.add hp _) _)
    (SourceLogic.add (SourceLogic.add hu _) _) (SourceLogic.add (SourceLogic.add he _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphInsert.uniquenessSentence) := ObjectGraphInsert.native_uniqueness
/-- 图限制的六个完整原核闭句，覆盖任意对象集合而非有限域。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRestriction.setSentence) := ObjectRestriction.native_set
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRestriction.functionSentence) := ObjectRestriction.native_function
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRestriction.edgeSentence) := ObjectRestriction.native_edge
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRestriction.uniqueSentence) := ObjectRestriction.native_unique
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRestriction.identitySentence) := ObjectRestriction.native_identity
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRestriction.composeSentence) := ObjectRestriction.native_compose

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectRestriction.functionSentence := ObjectRestriction.source_ZF_function
example : FirstOrder.Derives (TheoryTransport.theory ObjectRestriction.assumptions) []
    (Translation.sentence ObjectRestriction.functionSentence) := ObjectRestriction.function_kernel_certificate

example {n} (b d : Fin n) : Source.SetLanguage.subset b d = RestrictionSyntax.subset b d := RestrictionSyntax.subset_original b d

/-- 返回完整原functionOn，子域条件也使用原subset，均未作弱化。 -/
theorem restriction_is_original_function {n} {Γ : Source.Context n} (g f d b : Fin n)
    (hf : Source.Derives Γ (Source.SetLanguage.functionOn f d))
    (hb : Source.Derives Γ (Source.SetLanguage.subset b d))
    (hr : Source.Derives Γ (RestrictionSyntax.restrict g f b)) : Source.Derives Γ (Source.SetLanguage.functionOn g b) := by
  rw [GraphSyntax.functionOn_original] at hf ⊢
  rw [RestrictionSyntax.subset_original] at hb
  exact RestrictionFunction.function_restrict g f d b hf hb hr

/-- 相同变量槽的子域限制，不暗加b与d不同的条件。 -/
def selfRestrictionSentence : Source.Sentence :=
  ((GraphSyntax.functionOn (0 : Fin 2) 1).imp (RestrictionSyntax.existsRestriction 0 1)).close

theorem self_restriction : FirstOrder.Derives nativeZF [] (Translation.sentence selfRestrictionSentence) := by
  apply ObjectRestriction.native_replay
  apply TheoryTransport.sentence
  apply SourceAlgebra.close_derives
  apply Source.Derives.impI
  have he : Source.Derives (ObjectRestriction.assumptions.at 2) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
    .hyp ⟨_, Or.inl rfl, rfl⟩
  have hs : Source.Derives (ObjectRestriction.assumptions.at 2)
      ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) := .hyp ⟨_, Or.inr rfl, rfl⟩
  have hb : Source.Derives (Source.Context.add (GraphSyntax.functionOn 0 1) (ObjectRestriction.assumptions.at 2))
      (RestrictionSyntax.subset (1 : Fin 2) 1) := .allI (.impI (.hyp (Or.inl rfl)))
  exact RestrictionExistence.exists_function_restriction 0 1 1 (SourceLogic.add hs _) (SourceLogic.add he _) (.hyp (Or.inl rfl)) hb
/-- 任意内部集合族并图与实际定义域的六个原核闭句，包含空族。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphFamily.domainSentence) := ObjectGraphFamily.native_domain
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphFamily.domainUniqueSentence) := ObjectGraphFamily.native_domain_unique
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphFamily.unionSentence) := ObjectGraphFamily.native_union
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphFamily.uniqueSentence) := ObjectGraphFamily.native_unique
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphFamily.edgeSentence) := ObjectGraphFamily.native_edge
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphFamily.emptySentence) := ObjectGraphFamily.native_empty

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectGraphFamily.unionSentence := ObjectGraphFamily.source_ZF_union
example : FirstOrder.Derives (TheoryTransport.theory ObjectGraphFamily.assumptions) []
    (Translation.sentence ObjectGraphFamily.unionSentence) := ObjectGraphFamily.union_kernel_certificate

/-- 返回完整原functionOn，不把相容族并图弱化为单值关系。 -/
theorem family_union_is_original_function {n} {Γ : Source.Context n} (g d f : Fin n)
    (hu : Source.Derives Γ (InsertSyntax.unionOf g f)) (hd : Source.Derives Γ (GraphDomainSyntax.domain d g))
    (hf : Source.Derives Γ (GraphFamilySyntax.graphs f)) (hc : Source.Derives Γ (GraphFamilySyntax.compatible f)) :
    Source.Derives Γ (Source.SetLanguage.functionOn g d) := by
  rw [GraphSyntax.functionOn_original]
  exact GraphFamilyFunction.function_on g d f hu hd hf hc

/-- 输入界直接针对原Kuratowski/edge，不假设外部秩、良基或图有限。 -/
theorem edge_input_in_double_union {n} {Γ : Source.Context n} (g u v x y : Fin n)
    (hu : Source.Derives Γ (InsertSyntax.unionOf u g)) (hv : Source.Derives Γ (InsertSyntax.unionOf v u))
    (he : Source.Derives Γ (Source.SetLanguage.edge g x y)) : Source.Derives Γ (.mem x v) := by
  rw [GraphSyntax.edge_original] at he
  exact GraphDomainBound.edge_bound g u v x y hu hv he
/-- 原Infinity严格接入对象归纳集，未将宿主Nat作为对象ω。 -/
example : Source.SetLanguage.infinity = .ex (OmegaSyntax.isInductive (0 : Fin 1)) := OmegaSyntax.infinity_original

example : FirstOrder.Derives nativeZF [] (Translation.sentence OmegaSyntax.omegaExists) := ObjectOmega.native_existence
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmega.uniqueSentence) := ObjectOmega.native_unique
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmega.characterizationSentence) := ObjectOmega.native_characterization
example : Source.Derives (Source.SetLanguage.ZF.at 0) OmegaSyntax.omegaExists := ObjectOmega.source_ZF_existence

/-- 每个任意公式模式索引都有实际全参数闭句及原核推导。 -/
theorem all_object_omega_induction {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (OmegaInductionSyntax.sentence p)) := OmegaInduction.native_induction p

example {n} (p : Source.Formula (n+1)) :
    Source.Derives (Source.SetLanguage.ZF.at 0) (OmegaInductionSyntax.sentence p) := OmegaInduction.source_ZF_induction p

/-- 归纳逻辑核心只用该矩阵的一个分离实例；存在性三公理证书另行验收。 -/
example {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives (TheoryTransport.theory (OmegaInduction.assumptions p)) []
      (Translation.sentence (OmegaInductionSyntax.sentence p)) := OmegaInduction.kernel_certificate p

example : FirstOrder.Derives (TheoryTransport.theory ObjectOmega.assumptions) []
    (Translation.sentence OmegaSyntax.omegaExists) := ObjectOmega.existence_kernel_certificate

/-- 多参数、交错对象量词的实际归纳模式实例。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence (OmegaInductionSyntax.sentence parameterMatrix)) :=
  OmegaInduction.native_induction parameterMatrix
/-- 全部内部集合不自属，不预设宿主成员关系良基。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectIrreflexivity.sentence) := ObjectIrreflexivity.native_proof

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.decompositionSentence) := ObjectOmegaStructure.native_decomposition

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.transitiveSentence) := ObjectOmegaStructure.native_transitive

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.elementsSentence) := ObjectOmegaStructure.native_elements

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.zeroSentence) := ObjectOmegaStructure.native_zero

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.successorSentence) := ObjectOmegaStructure.native_successor

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.nonzeroSentence) := ObjectOmegaStructure.native_nonzero

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.injectiveSentence) := ObjectOmegaStructure.native_injective

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.freshSentence) := ObjectOmegaStructure.native_fresh

/-- 结构证书的有限公理集合没有加入Infinity、Replacement、Collection或AC。 -/
example : FirstOrder.Derives (TheoryTransport.theory ObjectOmegaStructure.assumptions) []
    (Translation.sentence ObjectOmegaStructure.injectiveSentence) := ObjectOmegaStructure.injective_kernel_certificate

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectOmegaStructure.freshSentence := ObjectOmegaStructure.source_ZF_fresh

/-- 全对象成员版本：归纳结果直接提供图扩展所需的新输入不自属见证。 -/
theorem internal_fresh_successor {n} {Γ : Source.Context n} (w x : Fin n)
    (hf : Source.Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hp : Source.Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hw : Source.Derives Γ (OmegaSyntax.omega w)) (hx : Source.Derives Γ (.mem x w)) :
    Source.Derives Γ (ObjectOmegaStructure.freshSuccessor w x) := ObjectOmegaStructure.fresh_successor w x hf hp hw hx

end PPAC.Migration.Step3Checks
