// Lean compiler output
// Module: Pancake.StageCompile
// Imports: public import Init public meta import Init public import Pancake.StageProg public import Pancake.StructModel
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
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageCompile_gNH___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageCompile_gNH___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageCompile_gNH___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageCompile_gNH___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageCompile_gNH(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageCompile_guarded(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageCompile_stC(lean_object*, lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageCompile_compile2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageCompile_compile2___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageCompile_compile2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageCompile_compile2___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageCompile_compile2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageCompile_gNH___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_unsigned_to_nat(64u);
v___x_3_ = l_BitVec_ofNat(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageCompile_gNH___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageCompile_gNH___closed__0, &lp_orb_x2dcompiler_Pancake_StageCompile_gNH___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StageCompile_gNH___closed__0);
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageCompile_gNH(lean_object* v_aHalt_6_){
_start:
{
uint8_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_7_ = 1;
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v_aHalt_6_);
v___x_9_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
v___x_10_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageCompile_gNH___closed__1, &lp_orb_x2dcompiler_Pancake_StageCompile_gNH___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageCompile_gNH___closed__1);
v___x_11_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_11_, 0, v___x_9_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
lean_ctor_set_uint8(v___x_11_, sizeof(void*)*2, v___x_7_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageCompile_guarded(lean_object* v_aHalt_12_, lean_object* v_frag_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lp_orb_x2dcompiler_Pancake_StageCompile_gNH(v_aHalt_12_);
v___x_15_ = lean_box(0);
v___x_16_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_16_, 0, v___x_14_);
lean_ctor_set(v___x_16_, 1, v_frag_13_);
lean_ctor_set(v___x_16_, 2, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageCompile_stC(lean_object* v_aAddr_17_, lean_object* v_v_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v_aAddr_17_);
v___x_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_20_, 0, v_v_18_);
v___x_21_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_21_, 0, v___x_19_);
lean_ctor_set(v___x_21_, 1, v___x_20_);
return v___x_21_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageCompile_compile2___closed__0(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = lean_unsigned_to_nat(64u);
v___x_24_ = l_BitVec_ofNat(v___x_23_, v___x_22_);
return v___x_24_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageCompile_compile2___closed__1(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageCompile_compile2___closed__0, &lp_orb_x2dcompiler_Pancake_StageCompile_compile2___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StageCompile_compile2___closed__0);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageCompile_compile2(lean_object* v_nm_27_, lean_object* v_aStat_28_, lean_object* v_aCnt_29_, lean_object* v_aBody_30_, lean_object* v_aHalt_31_, lean_object* v_x_32_){
_start:
{
switch(lean_obj_tag(v_x_32_))
{
case 2:
{
lean_object* v_code_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v_aBody_30_);
lean_dec(v_aCnt_29_);
lean_dec_ref(v_nm_27_);
v_code_33_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_code_33_);
lean_dec_ref(v_x_32_);
v___x_34_ = lean_unsigned_to_nat(64u);
v___x_35_ = l_BitVec_ofNat(v___x_34_, v_code_33_);
lean_dec(v_code_33_);
v___x_36_ = lp_orb_x2dcompiler_Pancake_StageCompile_stC(v_aStat_28_, v___x_35_);
v___x_37_ = lp_orb_x2dcompiler_Pancake_StageCompile_guarded(v_aHalt_31_, v___x_36_);
return v___x_37_;
}
case 3:
{
lean_object* v_c_38_; lean_object* v_code_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_56_; 
lean_dec(v_aBody_30_);
lean_dec(v_aCnt_29_);
v_c_38_ = lean_ctor_get(v_x_32_, 0);
v_code_39_ = lean_ctor_get(v_x_32_, 1);
v_isSharedCheck_56_ = !lean_is_exclusive(v_x_32_);
if (v_isSharedCheck_56_ == 0)
{
v___x_41_ = v_x_32_;
v_isShared_42_ = v_isSharedCheck_56_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_code_39_);
lean_inc(v_c_38_);
lean_dec(v_x_32_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_56_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_51_; 
v___x_43_ = lean_apply_1(v_nm_27_, v_c_38_);
v___x_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
v___x_45_ = lean_unsigned_to_nat(64u);
v___x_46_ = l_BitVec_ofNat(v___x_45_, v_code_39_);
lean_dec(v_code_39_);
v___x_47_ = lp_orb_x2dcompiler_Pancake_StageCompile_stC(v_aStat_28_, v___x_46_);
v___x_48_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageCompile_compile2___closed__0, &lp_orb_x2dcompiler_Pancake_StageCompile_compile2___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StageCompile_compile2___closed__0);
lean_inc(v_aHalt_31_);
v___x_49_ = lp_orb_x2dcompiler_Pancake_StageCompile_stC(v_aHalt_31_, v___x_48_);
if (v_isShared_42_ == 0)
{
lean_ctor_set_tag(v___x_41_, 5);
lean_ctor_set(v___x_41_, 1, v___x_49_);
lean_ctor_set(v___x_41_, 0, v___x_47_);
v___x_51_ = v___x_41_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_47_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v___x_49_);
v___x_51_ = v_reuseFailAlloc_55_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_box(0);
v___x_53_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_53_, 0, v___x_44_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
lean_ctor_set(v___x_53_, 2, v___x_52_);
v___x_54_ = lp_orb_x2dcompiler_Pancake_StageCompile_guarded(v_aHalt_31_, v___x_53_);
return v___x_54_;
}
}
}
case 4:
{
lean_object* v_t_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_87_; 
lean_dec(v_aCnt_29_);
lean_dec(v_aStat_28_);
lean_dec_ref(v_nm_27_);
v_t_57_ = lean_ctor_get(v_x_32_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v_x_32_);
if (v_isSharedCheck_87_ == 0)
{
v___x_59_ = v_x_32_;
v_isShared_60_ = v_isSharedCheck_87_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_t_57_);
lean_dec(v_x_32_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_87_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
switch(lean_obj_tag(v_t_57_))
{
case 0:
{
lean_object* v___x_61_; 
lean_del_object(v___x_59_);
lean_dec(v_aHalt_31_);
lean_dec(v_aBody_30_);
v___x_61_ = lean_box(0);
return v___x_61_;
}
case 1:
{
lean_object* v_b_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
lean_del_object(v___x_59_);
v_b_62_ = lean_ctor_get(v_t_57_, 0);
lean_inc(v_b_62_);
lean_dec_ref(v_t_57_);
v___x_63_ = lean_unsigned_to_nat(64u);
v___x_64_ = l_List_lengthTR___redArg(v_b_62_);
lean_dec(v_b_62_);
v___x_65_ = l_BitVec_ofNat(v___x_63_, v___x_64_);
lean_dec(v___x_64_);
v___x_66_ = lp_orb_x2dcompiler_Pancake_StageCompile_stC(v_aBody_30_, v___x_65_);
v___x_67_ = lp_orb_x2dcompiler_Pancake_StageCompile_guarded(v_aHalt_31_, v___x_66_);
return v___x_67_;
}
default: 
{
lean_object* v_b_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_86_; 
v_b_68_ = lean_ctor_get(v_t_57_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v_t_57_);
if (v_isSharedCheck_86_ == 0)
{
v___x_70_ = v_t_57_;
v_isShared_71_ = v_isSharedCheck_86_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_b_68_);
lean_dec(v_t_57_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_86_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_73_; 
if (v_isShared_71_ == 0)
{
lean_ctor_set_tag(v___x_70_, 0);
lean_ctor_set(v___x_70_, 0, v_aBody_30_);
v___x_73_ = v___x_70_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_aBody_30_);
v___x_73_ = v_reuseFailAlloc_85_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
uint8_t v___x_74_; lean_object* v___x_76_; 
v___x_74_ = 0;
lean_inc_ref(v___x_73_);
if (v_isShared_60_ == 0)
{
lean_ctor_set_tag(v___x_59_, 7);
lean_ctor_set(v___x_59_, 0, v___x_73_);
v___x_76_ = v___x_59_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_73_);
v___x_76_ = v_reuseFailAlloc_84_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_77_ = lean_unsigned_to_nat(64u);
v___x_78_ = l_List_lengthTR___redArg(v_b_68_);
lean_dec(v_b_68_);
v___x_79_ = l_BitVec_ofNat(v___x_77_, v___x_78_);
lean_dec(v___x_78_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
v___x_81_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_81_, 0, v___x_76_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*2, v___x_74_);
v___x_82_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_73_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = lp_orb_x2dcompiler_Pancake_StageCompile_guarded(v_aHalt_31_, v___x_82_);
return v___x_83_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_a_88_; lean_object* v_b_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_98_; 
v_a_88_ = lean_ctor_get(v_x_32_, 0);
v_b_89_ = lean_ctor_get(v_x_32_, 1);
v_isSharedCheck_98_ = !lean_is_exclusive(v_x_32_);
if (v_isSharedCheck_98_ == 0)
{
v___x_91_ = v_x_32_;
v_isShared_92_ = v_isSharedCheck_98_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_b_89_);
lean_inc(v_a_88_);
lean_dec(v_x_32_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_98_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
lean_inc(v_aHalt_31_);
lean_inc(v_aBody_30_);
lean_inc(v_aCnt_29_);
lean_inc(v_aStat_28_);
lean_inc_ref(v_nm_27_);
v___x_93_ = lp_orb_x2dcompiler_Pancake_StageCompile_compile2(v_nm_27_, v_aStat_28_, v_aCnt_29_, v_aBody_30_, v_aHalt_31_, v_a_88_);
v___x_94_ = lp_orb_x2dcompiler_Pancake_StageCompile_compile2(v_nm_27_, v_aStat_28_, v_aCnt_29_, v_aBody_30_, v_aHalt_31_, v_b_89_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v___x_94_);
lean_ctor_set(v___x_91_, 0, v___x_93_);
v___x_96_ = v___x_91_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v___x_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
case 6:
{
lean_object* v_c_99_; lean_object* v_a_100_; lean_object* v_b_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_112_; 
v_c_99_ = lean_ctor_get(v_x_32_, 0);
v_a_100_ = lean_ctor_get(v_x_32_, 1);
v_b_101_ = lean_ctor_get(v_x_32_, 2);
v_isSharedCheck_112_ = !lean_is_exclusive(v_x_32_);
if (v_isSharedCheck_112_ == 0)
{
v___x_103_ = v_x_32_;
v_isShared_104_ = v_isSharedCheck_112_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_b_101_);
lean_inc(v_a_100_);
lean_inc(v_c_99_);
lean_dec(v_x_32_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_112_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
lean_inc_ref_n(v_nm_27_, 2);
v___x_105_ = lean_apply_1(v_nm_27_, v_c_99_);
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_inc(v_aHalt_31_);
lean_inc(v_aBody_30_);
lean_inc(v_aCnt_29_);
lean_inc(v_aStat_28_);
v___x_107_ = lp_orb_x2dcompiler_Pancake_StageCompile_compile2(v_nm_27_, v_aStat_28_, v_aCnt_29_, v_aBody_30_, v_aHalt_31_, v_a_100_);
v___x_108_ = lp_orb_x2dcompiler_Pancake_StageCompile_compile2(v_nm_27_, v_aStat_28_, v_aCnt_29_, v_aBody_30_, v_aHalt_31_, v_b_101_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 2, v___x_108_);
lean_ctor_set(v___x_103_, 1, v___x_107_);
lean_ctor_set(v___x_103_, 0, v___x_106_);
v___x_110_ = v___x_103_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_106_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_111_, 2, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
default: 
{
lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec_ref(v_x_32_);
lean_dec(v_aBody_30_);
lean_dec(v_aStat_28_);
lean_dec_ref(v_nm_27_);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v_aCnt_29_);
v___x_114_ = 0;
lean_inc_ref(v___x_113_);
v___x_115_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
v___x_116_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageCompile_compile2___closed__1, &lp_orb_x2dcompiler_Pancake_StageCompile_compile2___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageCompile_compile2___closed__1);
v___x_117_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*2, v___x_114_);
v___x_118_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_113_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = lp_orb_x2dcompiler_Pancake_StageCompile_guarded(v_aHalt_31_, v___x_118_);
return v___x_119_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_StageProg(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_StructModel(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_StageCompile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_StageProg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_StructModel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
