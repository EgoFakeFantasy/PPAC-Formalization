# 本地工作进度（2026-11-08）

## 本批验收（2026-11-08）：原阶段9的源复合／逆名字图

固定 RelationCalculus:200–359 已迁移至 ForcingMapCalculus。两个 nativeZF／FirstOrder.Derives 原核存在句分别实际构造对应源元组的稳定子 S 和原始 HS 图 J，保留子群／滤子、精确 tupleFixed、原始收集器及同一支撑。复合图在任意内部条件下保留两份完整原 mapsTo／surjection／injection 输入并证明对应结论；逆图在完整源双射输入下证明完整满射／单射。Total/One/Onto/Injective、移动／同余／正则及应用定律均已消去，不作为输入。

复用现成关系图、稳定子、强迫对称／同余及函数定理；将已有完整函数消去公开为四项别名，原有证明正文逐字节保留。这里迁移的是源 HS 名字图，不以地面置换图或序数最小值逆图代替。下一项仍为 UniformImages.nonwellorderable_image_bijection:243–276 的同一系统连接；序数和完整非良序商结论已有，不重新证明。

完整本地验收：3202 构建任务、37265 项声明；全部37224项旧足迹不变，41项新增；9条命令（5条trust=0）均退出0，零警告、无新增公理依赖，且本批未依赖对象 Choice 证书；2760个规范文本哈希已复核。报告：verification/map-calculus-acceptance.json。

远端兼容修复 bc9367f 的完整 Linux CI 已成功：37209 项声明、零警告，依赖／源码回归及完整原核检查均通过。已上传上一批像商图 7352330，其 CI 正在完整构建，固定检出和源码检查已通过。本批先本地保存，避免叠加触发。远端运行与当前本地批次分别记录。

仍在原阶段9。非良序像双射及 SVC、ACwo、全局商编码单射、¬AC 模型应用尚未全部闭合；第10 PP/Main／全部内部与非标准证明码Con、第11终验及原第4 Comparator仍未完成。最终对象Con未证明。



本分支迁移固定 OpenAI PPAC 源证明到 YesMetaZFC 的原对象推导核，继续采用原计划 1–11 阶段。原第 8 阶段的全局装配门已通过；当前为第 9 阶段，固定源kernelGraph／同值类／imageClassRelation、实际像商图及源复合／逆图已迁移，最终目标尚未完成。

最终目标：`FirstOrder.Derives nativeZF [] (Con_ZF → Con_U)`，其中 `U = ZF + PP + ACwo + ¬AC`。内部 Con 必须覆盖全部内部证明编码，包括非标准编码。

## 必要的后续工作

1. 第9阶段：继续固定源非良序像双射:243–276；随后在同一系统完成SVC、ACwo、全局商编码单射和¬AC。kernel、完整imageClassRelation、实际imageQuotient及像图的完整函数定律均已完成；复用现有关系图构造、完整函数定律、序数及原非良序商双射；RelationCalculus 的逆／复合名字图也已迁移，接下来实际连接非良序像双射。
2. 第 10 阶段：接通完整 PP/Main，复用 ZF/U 的既有 Proof/Sat 配套完成全部内部／非标准矛盾码传输及最终 Con。
3. 第 11 阶段：最终对象推导主句、干净检出复现及剩余验收；原第 4 阶段 OpenAI Comparator 仍单列未验收。

复用 YesMetaZFC 与已固定伴随仓库中已有的 L 解释、全体公理模式、递归及 ProofSat 基础。不得把这些已存在的基础重新列为待从头实现。
