// Lean compiler output
// Module: Pancake.LowerBridge
// Imports: public import Init public meta import Init public import Pancake.ServeEmit public import Pancake.Lower
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeEmit_storesInto_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridge_addrModel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridge_addrModel___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridge_storesIntoL(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridge_storesModel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridge_0__Pancake_Lower_lowerStmtsFold_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridge_0__Pancake_Lower_lowerStmtsFold_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridge_0__Pancake_Lower_lowerStmt1_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridge_0__Pancake_Lower_lowerStmt1_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridge_0__Pancake_Lower_lowerStmtsFold_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridge_0__Pancake_Lower_lowerStmtsFold_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridge_storeByteCount(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridge_storeByteCount___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridge_addrModel(lean_object* v_dst_1_, lean_object* v_k_2_){
_start:
{
lean_object* v___x_3_; uint8_t v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_nat_dec_eq(v_k_2_, v___x_3_);
if (v___x_4_ == 0)
{
uint8_t v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_5_ = 0;
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v_dst_1_);
v___x_7_ = lean_unsigned_to_nat(64u);
v___x_8_ = l_BitVec_ofNat(v___x_7_, v_k_2_);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
v___x_10_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_10_, 0, v___x_6_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
lean_ctor_set_uint8(v___x_10_, sizeof(void*)*2, v___x_5_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; 
v___x_11_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_11_, 0, v_dst_1_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridge_addrModel___boxed(lean_object* v_dst_12_, lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_orb_x2dcompiler_Pancake_LowerBridge_addrModel(v_dst_12_, v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridge_storesIntoL(lean_object* v_dst_15_, lean_object* v_ps_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_box(0);
v___x_18_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeEmit_storesInto_spec__0(v_dst_15_, v_ps_16_, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridge_storesModel(lean_object* v_dst_19_, lean_object* v_x_20_){
_start:
{
if (lean_obj_tag(v_x_20_) == 0)
{
lean_object* v___x_21_; 
lean_dec_ref(v_dst_19_);
v___x_21_ = lean_box(0);
return v___x_21_;
}
else
{
lean_object* v_tail_22_; 
v_tail_22_ = lean_ctor_get(v_x_20_, 1);
if (lean_obj_tag(v_tail_22_) == 0)
{
lean_object* v_head_23_; lean_object* v_fst_24_; lean_object* v_snd_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_36_; 
v_head_23_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_head_23_);
lean_dec_ref(v_x_20_);
v_fst_24_ = lean_ctor_get(v_head_23_, 0);
v_snd_25_ = lean_ctor_get(v_head_23_, 1);
v_isSharedCheck_36_ = !lean_is_exclusive(v_head_23_);
if (v_isSharedCheck_36_ == 0)
{
v___x_27_ = v_head_23_;
v_isShared_28_ = v_isSharedCheck_36_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_snd_25_);
lean_inc(v_fst_24_);
lean_dec(v_head_23_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_36_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_29_ = lp_orb_x2dcompiler_Pancake_LowerBridge_addrModel(v_dst_19_, v_fst_24_);
lean_dec(v_fst_24_);
v___x_30_ = lean_unsigned_to_nat(64u);
v___x_31_ = l_BitVec_ofNat(v___x_30_, v_snd_25_);
lean_dec(v_snd_25_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
if (v_isShared_28_ == 0)
{
lean_ctor_set_tag(v___x_27_, 9);
lean_ctor_set(v___x_27_, 1, v___x_32_);
lean_ctor_set(v___x_27_, 0, v___x_29_);
v___x_34_ = v___x_27_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v___x_32_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
else
{
lean_object* v_head_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_58_; 
lean_inc(v_tail_22_);
v_head_37_ = lean_ctor_get(v_x_20_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v_x_20_);
if (v_isSharedCheck_58_ == 0)
{
lean_object* v_unused_59_; 
v_unused_59_ = lean_ctor_get(v_x_20_, 1);
lean_dec(v_unused_59_);
v___x_39_ = v_x_20_;
v_isShared_40_ = v_isSharedCheck_58_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_head_37_);
lean_dec(v_x_20_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_58_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v_fst_41_; lean_object* v_snd_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_57_; 
v_fst_41_ = lean_ctor_get(v_head_37_, 0);
v_snd_42_ = lean_ctor_get(v_head_37_, 1);
v_isSharedCheck_57_ = !lean_is_exclusive(v_head_37_);
if (v_isSharedCheck_57_ == 0)
{
v___x_44_ = v_head_37_;
v_isShared_45_ = v_isSharedCheck_57_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_snd_42_);
lean_inc(v_fst_41_);
lean_dec(v_head_37_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_57_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_51_; 
lean_inc_ref(v_dst_19_);
v___x_46_ = lp_orb_x2dcompiler_Pancake_LowerBridge_addrModel(v_dst_19_, v_fst_41_);
lean_dec(v_fst_41_);
v___x_47_ = lean_unsigned_to_nat(64u);
v___x_48_ = l_BitVec_ofNat(v___x_47_, v_snd_42_);
lean_dec(v_snd_42_);
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
if (v_isShared_45_ == 0)
{
lean_ctor_set_tag(v___x_44_, 9);
lean_ctor_set(v___x_44_, 1, v___x_49_);
lean_ctor_set(v___x_44_, 0, v___x_46_);
v___x_51_ = v___x_44_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v___x_49_);
v___x_51_ = v_reuseFailAlloc_56_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_52_ = lp_orb_x2dcompiler_Pancake_LowerBridge_storesModel(v_dst_19_, v_tail_22_);
if (v_isShared_40_ == 0)
{
lean_ctor_set_tag(v___x_39_, 5);
lean_ctor_set(v___x_39_, 1, v___x_52_);
lean_ctor_set(v___x_39_, 0, v___x_51_);
v___x_54_ = v___x_39_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_51_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridge_0__Pancake_Lower_lowerStmtsFold_match__3_splitter___redArg(lean_object* v_x_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_, lean_object* v_h__3_63_, lean_object* v_h__4_64_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec(v_h__4_64_);
lean_dec(v_h__3_63_);
lean_dec(v_h__2_62_);
v___x_65_ = lean_box(0);
v___x_66_ = lean_apply_1(v_h__1_61_, v___x_65_);
return v___x_66_;
}
else
{
lean_object* v_tail_67_; 
lean_dec(v_h__1_61_);
v_tail_67_ = lean_ctor_get(v_x_60_, 1);
if (lean_obj_tag(v_tail_67_) == 0)
{
lean_object* v_head_68_; lean_object* v___x_69_; 
lean_dec(v_h__4_64_);
lean_dec(v_h__3_63_);
v_head_68_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_head_68_);
lean_dec_ref(v_x_60_);
v___x_69_ = lean_apply_1(v_h__2_62_, v_head_68_);
return v___x_69_;
}
else
{
lean_object* v_head_70_; 
lean_inc(v_tail_67_);
lean_dec(v_h__2_62_);
v_head_70_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_head_70_);
lean_dec_ref(v_x_60_);
if (lean_obj_tag(v_head_70_) == 0)
{
lean_object* v_name_71_; lean_object* v_val_72_; lean_object* v___x_73_; 
lean_dec(v_h__4_64_);
v_name_71_ = lean_ctor_get(v_head_70_, 0);
lean_inc_ref(v_name_71_);
v_val_72_ = lean_ctor_get(v_head_70_, 1);
lean_inc(v_val_72_);
lean_dec_ref(v_head_70_);
v___x_73_ = lean_apply_4(v_h__3_63_, v_name_71_, v_val_72_, v_tail_67_, lean_box(0));
return v___x_73_;
}
else
{
lean_object* v___x_74_; 
lean_dec(v_h__3_63_);
v___x_74_ = lean_apply_4(v_h__4_64_, v_head_70_, v_tail_67_, lean_box(0), lean_box(0));
return v___x_74_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridge_0__Pancake_Lower_lowerStmtsFold_match__3_splitter(lean_object* v_motive_75_, lean_object* v_x_76_, lean_object* v_h__1_77_, lean_object* v_h__2_78_, lean_object* v_h__3_79_, lean_object* v_h__4_80_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_h__4_80_);
lean_dec(v_h__3_79_);
lean_dec(v_h__2_78_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_apply_1(v_h__1_77_, v___x_81_);
return v___x_82_;
}
else
{
lean_object* v_tail_83_; 
lean_dec(v_h__1_77_);
v_tail_83_ = lean_ctor_get(v_x_76_, 1);
if (lean_obj_tag(v_tail_83_) == 0)
{
lean_object* v_head_84_; lean_object* v___x_85_; 
lean_dec(v_h__4_80_);
lean_dec(v_h__3_79_);
v_head_84_ = lean_ctor_get(v_x_76_, 0);
lean_inc(v_head_84_);
lean_dec_ref(v_x_76_);
v___x_85_ = lean_apply_1(v_h__2_78_, v_head_84_);
return v___x_85_;
}
else
{
lean_object* v_head_86_; 
lean_inc(v_tail_83_);
lean_dec(v_h__2_78_);
v_head_86_ = lean_ctor_get(v_x_76_, 0);
lean_inc(v_head_86_);
lean_dec_ref(v_x_76_);
if (lean_obj_tag(v_head_86_) == 0)
{
lean_object* v_name_87_; lean_object* v_val_88_; lean_object* v___x_89_; 
lean_dec(v_h__4_80_);
v_name_87_ = lean_ctor_get(v_head_86_, 0);
lean_inc_ref(v_name_87_);
v_val_88_ = lean_ctor_get(v_head_86_, 1);
lean_inc(v_val_88_);
lean_dec_ref(v_head_86_);
v___x_89_ = lean_apply_4(v_h__3_79_, v_name_87_, v_val_88_, v_tail_83_, lean_box(0));
return v___x_89_;
}
else
{
lean_object* v___x_90_; 
lean_dec(v_h__3_79_);
v___x_90_ = lean_apply_4(v_h__4_80_, v_head_86_, v_tail_83_, lean_box(0), lean_box(0));
return v___x_90_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridge_0__Pancake_Lower_lowerStmt1_match__5_splitter___redArg(lean_object* v_x_91_, lean_object* v_x_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_){
_start:
{
if (lean_obj_tag(v_x_91_) == 1)
{
if (lean_obj_tag(v_x_92_) == 1)
{
lean_object* v_val_95_; lean_object* v_val_96_; lean_object* v___x_97_; 
lean_dec(v_h__2_94_);
v_val_95_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_val_95_);
lean_dec_ref(v_x_91_);
v_val_96_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_val_96_);
lean_dec_ref(v_x_92_);
v___x_97_ = lean_apply_2(v_h__1_93_, v_val_95_, v_val_96_);
return v___x_97_;
}
else
{
lean_object* v___x_98_; 
lean_dec(v_h__1_93_);
v___x_98_ = lean_apply_3(v_h__2_94_, v_x_91_, v_x_92_, lean_box(0));
return v___x_98_;
}
}
else
{
lean_object* v___x_99_; 
lean_dec(v_h__1_93_);
v___x_99_ = lean_apply_3(v_h__2_94_, v_x_91_, v_x_92_, lean_box(0));
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridge_0__Pancake_Lower_lowerStmt1_match__5_splitter(lean_object* v_motive_100_, lean_object* v_x_101_, lean_object* v_x_102_, lean_object* v_h__1_103_, lean_object* v_h__2_104_){
_start:
{
if (lean_obj_tag(v_x_101_) == 1)
{
if (lean_obj_tag(v_x_102_) == 1)
{
lean_object* v_val_105_; lean_object* v_val_106_; lean_object* v___x_107_; 
lean_dec(v_h__2_104_);
v_val_105_ = lean_ctor_get(v_x_101_, 0);
lean_inc(v_val_105_);
lean_dec_ref(v_x_101_);
v_val_106_ = lean_ctor_get(v_x_102_, 0);
lean_inc(v_val_106_);
lean_dec_ref(v_x_102_);
v___x_107_ = lean_apply_2(v_h__1_103_, v_val_105_, v_val_106_);
return v___x_107_;
}
else
{
lean_object* v___x_108_; 
lean_dec(v_h__1_103_);
v___x_108_ = lean_apply_3(v_h__2_104_, v_x_101_, v_x_102_, lean_box(0));
return v___x_108_;
}
}
else
{
lean_object* v___x_109_; 
lean_dec(v_h__1_103_);
v___x_109_ = lean_apply_3(v_h__2_104_, v_x_101_, v_x_102_, lean_box(0));
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridge_0__Pancake_Lower_lowerStmtsFold_match__1_splitter___redArg(lean_object* v_x_110_, lean_object* v_x_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_){
_start:
{
if (lean_obj_tag(v_x_110_) == 1)
{
if (lean_obj_tag(v_x_111_) == 1)
{
lean_object* v_val_114_; lean_object* v_val_115_; lean_object* v___x_116_; 
lean_dec(v_h__2_113_);
v_val_114_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_val_114_);
lean_dec_ref(v_x_110_);
v_val_115_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_val_115_);
lean_dec_ref(v_x_111_);
v___x_116_ = lean_apply_2(v_h__1_112_, v_val_114_, v_val_115_);
return v___x_116_;
}
else
{
lean_object* v___x_117_; 
lean_dec(v_h__1_112_);
v___x_117_ = lean_apply_3(v_h__2_113_, v_x_110_, v_x_111_, lean_box(0));
return v___x_117_;
}
}
else
{
lean_object* v___x_118_; 
lean_dec(v_h__1_112_);
v___x_118_ = lean_apply_3(v_h__2_113_, v_x_110_, v_x_111_, lean_box(0));
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridge_0__Pancake_Lower_lowerStmtsFold_match__1_splitter(lean_object* v_motive_119_, lean_object* v_x_120_, lean_object* v_x_121_, lean_object* v_h__1_122_, lean_object* v_h__2_123_){
_start:
{
if (lean_obj_tag(v_x_120_) == 1)
{
if (lean_obj_tag(v_x_121_) == 1)
{
lean_object* v_val_124_; lean_object* v_val_125_; lean_object* v___x_126_; 
lean_dec(v_h__2_123_);
v_val_124_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_val_124_);
lean_dec_ref(v_x_120_);
v_val_125_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_val_125_);
lean_dec_ref(v_x_121_);
v___x_126_ = lean_apply_2(v_h__1_122_, v_val_124_, v_val_125_);
return v___x_126_;
}
else
{
lean_object* v___x_127_; 
lean_dec(v_h__1_122_);
v___x_127_ = lean_apply_3(v_h__2_123_, v_x_120_, v_x_121_, lean_box(0));
return v___x_127_;
}
}
else
{
lean_object* v___x_128_; 
lean_dec(v_h__1_122_);
v___x_128_ = lean_apply_3(v_h__2_123_, v_x_120_, v_x_121_, lean_box(0));
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridge_storeByteCount(lean_object* v_x_129_){
_start:
{
switch(lean_obj_tag(v_x_129_))
{
case 9:
{
lean_object* v___x_130_; 
v___x_130_ = lean_unsigned_to_nat(1u);
return v___x_130_;
}
case 5:
{
lean_object* v_c1_131_; lean_object* v_c2_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_c1_131_ = lean_ctor_get(v_x_129_, 0);
v_c2_132_ = lean_ctor_get(v_x_129_, 1);
v___x_133_ = lp_orb_x2dcompiler_Pancake_LowerBridge_storeByteCount(v_c1_131_);
v___x_134_ = lp_orb_x2dcompiler_Pancake_LowerBridge_storeByteCount(v_c2_132_);
v___x_135_ = lean_nat_add(v___x_133_, v___x_134_);
lean_dec(v___x_134_);
lean_dec(v___x_133_);
return v___x_135_;
}
default: 
{
lean_object* v___x_136_; 
v___x_136_ = lean_unsigned_to_nat(0u);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridge_storeByteCount___boxed(lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = lp_orb_x2dcompiler_Pancake_LowerBridge_storeByteCount(v_x_137_);
lean_dec(v_x_137_);
return v_res_138_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_ServeEmit(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_Lower(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_LowerBridge(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_ServeEmit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_Lower(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
