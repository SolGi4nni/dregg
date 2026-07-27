// Lean compiler output
// Module: Pancake.SerializeFull
// Imports: public import Init public meta import Init public import Pancake.SerializeCompile public import Pancake.StructModel
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
lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLineOf(lean_object*);
extern lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_headerBlockOf(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dst"};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "src"};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__5;
static const lean_string_object lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "len"};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__6_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_totalLen(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_totalLen___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_concatSegs(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_SerializeFull_0__Pancake_SerializeFull_totalLen_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_SerializeFull_0__Pancake_SerializeFull_totalLen_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSegs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSegs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_statusSeg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_statusSeg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_headerSeg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_headerSeg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_respSegs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_respSegs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__3(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = lean_unsigned_to_nat(64u);
v___x_6_ = l_BitVec_ofNat(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__4(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__3, &lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__3);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__5(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__4, &lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__4);
v___x_10_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__2));
v___x_11_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg(lean_object* v_base_13_, lean_object* v_off_14_, lean_object* v_srcSeg_15_, lean_object* v_len_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_17_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__0));
v___x_18_ = lean_unsigned_to_nat(64u);
v___x_19_ = l_BitVec_ofNat(v___x_18_, v_off_14_);
v___x_20_ = l_BitVec_add(v___x_18_, v_base_13_, v___x_19_);
lean_dec(v___x_19_);
v___x_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
v___x_22_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_22_, 0, v___x_17_);
lean_ctor_set(v___x_22_, 1, v___x_21_);
v___x_23_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__1));
v___x_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_24_, 0, v_srcSeg_15_);
v___x_25_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_23_);
lean_ctor_set(v___x_25_, 1, v___x_24_);
v___x_26_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__5, &lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__5);
v___x_27_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___closed__6));
v___x_28_ = l_BitVec_ofNat(v___x_18_, v_len_16_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
v___x_30_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_27_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
v___x_31_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile;
v___x_32_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_30_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
v___x_33_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_26_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
v___x_34_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_25_);
lean_ctor_set(v___x_34_, 1, v___x_33_);
v___x_35_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_22_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg___boxed(lean_object* v_base_36_, lean_object* v_off_37_, lean_object* v_srcSeg_38_, lean_object* v_len_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg(v_base_36_, v_off_37_, v_srcSeg_38_, v_len_39_);
lean_dec(v_len_39_);
lean_dec(v_off_37_);
lean_dec(v_base_36_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_totalLen(lean_object* v_x_41_){
_start:
{
if (lean_obj_tag(v_x_41_) == 0)
{
lean_object* v___x_42_; 
v___x_42_ = lean_unsigned_to_nat(0u);
return v___x_42_;
}
else
{
lean_object* v_head_43_; lean_object* v_tail_44_; lean_object* v_snd_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_head_43_ = lean_ctor_get(v_x_41_, 0);
v_tail_44_ = lean_ctor_get(v_x_41_, 1);
v_snd_45_ = lean_ctor_get(v_head_43_, 1);
v___x_46_ = l_List_lengthTR___redArg(v_snd_45_);
v___x_47_ = lp_orb_x2dcompiler_Pancake_SerializeFull_totalLen(v_tail_44_);
v___x_48_ = lean_nat_add(v___x_46_, v___x_47_);
lean_dec(v___x_47_);
lean_dec(v___x_46_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_totalLen___boxed(lean_object* v_x_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_orb_x2dcompiler_Pancake_SerializeFull_totalLen(v_x_49_);
lean_dec(v_x_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_concatSegs(lean_object* v_x_51_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
lean_object* v___x_52_; 
v___x_52_ = lean_box(0);
return v___x_52_;
}
else
{
lean_object* v_head_53_; lean_object* v_tail_54_; lean_object* v_snd_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_head_53_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_head_53_);
v_tail_54_ = lean_ctor_get(v_x_51_, 1);
lean_inc(v_tail_54_);
lean_dec_ref(v_x_51_);
v_snd_55_ = lean_ctor_get(v_head_53_, 1);
lean_inc(v_snd_55_);
lean_dec(v_head_53_);
v___x_56_ = lp_orb_x2dcompiler_Pancake_SerializeFull_concatSegs(v_tail_54_);
v___x_57_ = l_List_appendTR___redArg(v_snd_55_, v___x_56_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_SerializeFull_0__Pancake_SerializeFull_totalLen_match__1_splitter___redArg(lean_object* v_x_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec(v_h__2_60_);
v___x_61_ = lean_box(0);
v___x_62_ = lean_apply_1(v_h__1_59_, v___x_61_);
return v___x_62_;
}
else
{
lean_object* v_head_63_; lean_object* v_tail_64_; lean_object* v_fst_65_; lean_object* v_snd_66_; lean_object* v___x_67_; 
lean_dec(v_h__1_59_);
v_head_63_ = lean_ctor_get(v_x_58_, 0);
lean_inc(v_head_63_);
v_tail_64_ = lean_ctor_get(v_x_58_, 1);
lean_inc(v_tail_64_);
lean_dec_ref(v_x_58_);
v_fst_65_ = lean_ctor_get(v_head_63_, 0);
lean_inc(v_fst_65_);
v_snd_66_ = lean_ctor_get(v_head_63_, 1);
lean_inc(v_snd_66_);
lean_dec(v_head_63_);
v___x_67_ = lean_apply_3(v_h__2_60_, v_fst_65_, v_snd_66_, v_tail_64_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_SerializeFull_0__Pancake_SerializeFull_totalLen_match__1_splitter(lean_object* v_motive_68_, lean_object* v_x_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_h__2_71_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_apply_1(v_h__1_70_, v___x_72_);
return v___x_73_;
}
else
{
lean_object* v_head_74_; lean_object* v_tail_75_; lean_object* v_fst_76_; lean_object* v_snd_77_; lean_object* v___x_78_; 
lean_dec(v_h__1_70_);
v_head_74_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_head_74_);
v_tail_75_ = lean_ctor_get(v_x_69_, 1);
lean_inc(v_tail_75_);
lean_dec_ref(v_x_69_);
v_fst_76_ = lean_ctor_get(v_head_74_, 0);
lean_inc(v_fst_76_);
v_snd_77_ = lean_ctor_get(v_head_74_, 1);
lean_inc(v_snd_77_);
lean_dec(v_head_74_);
v___x_78_ = lean_apply_3(v_h__2_71_, v_fst_76_, v_snd_77_, v_tail_75_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSegs(lean_object* v_base_79_, lean_object* v_x_80_, lean_object* v_x_81_){
_start:
{
if (lean_obj_tag(v_x_81_) == 0)
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(0);
return v___x_82_;
}
else
{
lean_object* v_head_83_; lean_object* v_tail_84_; lean_object* v_fst_85_; lean_object* v_snd_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_97_; 
v_head_83_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_head_83_);
v_tail_84_ = lean_ctor_get(v_x_81_, 1);
lean_inc(v_tail_84_);
lean_dec_ref(v_x_81_);
v_fst_85_ = lean_ctor_get(v_head_83_, 0);
v_snd_86_ = lean_ctor_get(v_head_83_, 1);
v_isSharedCheck_97_ = !lean_is_exclusive(v_head_83_);
if (v_isSharedCheck_97_ == 0)
{
v___x_88_ = v_head_83_;
v_isShared_89_ = v_isSharedCheck_97_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_snd_86_);
lean_inc(v_fst_85_);
lean_dec(v_head_83_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_97_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_90_ = l_List_lengthTR___redArg(v_snd_86_);
lean_dec(v_snd_86_);
v___x_91_ = lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg(v_base_79_, v_x_80_, v_fst_85_, v___x_90_);
v___x_92_ = lean_nat_add(v_x_80_, v___x_90_);
lean_dec(v___x_90_);
v___x_93_ = lp_orb_x2dcompiler_Pancake_SerializeFull_writeSegs(v_base_79_, v___x_92_, v_tail_84_);
lean_dec(v___x_92_);
if (v_isShared_89_ == 0)
{
lean_ctor_set_tag(v___x_88_, 5);
lean_ctor_set(v___x_88_, 1, v___x_93_);
lean_ctor_set(v___x_88_, 0, v___x_91_);
v___x_95_ = v___x_88_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSegs___boxed(lean_object* v_base_98_, lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = lp_orb_x2dcompiler_Pancake_SerializeFull_writeSegs(v_base_98_, v_x_99_, v_x_100_);
lean_dec(v_x_99_);
lean_dec(v_base_98_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_statusSeg(lean_object* v_resp_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLineOf(v_resp_102_);
v___x_104_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf;
v___x_105_ = l_List_appendTR___redArg(v___x_103_, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_statusSeg___boxed(lean_object* v_resp_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = lp_orb_x2dcompiler_Pancake_SerializeFull_statusSeg(v_resp_106_);
lean_dec_ref(v_resp_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_headerSeg(lean_object* v_resp_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_109_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_headerBlockOf(v_resp_108_);
v___x_110_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf;
v___x_111_ = l_List_appendTR___redArg(v___x_109_, v___x_110_);
v___x_112_ = l_List_appendTR___redArg(v___x_111_, v___x_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_headerSeg___boxed(lean_object* v_resp_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = lp_orb_x2dcompiler_Pancake_SerializeFull_headerSeg(v_resp_113_);
lean_dec_ref(v_resp_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_respSegs(lean_object* v_resp_115_, lean_object* v_srcS_116_, lean_object* v_srcH_117_, lean_object* v_srcB_118_){
_start:
{
lean_object* v_body_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_body_119_ = lean_ctor_get(v_resp_115_, 3);
v___x_120_ = lp_orb_x2dcompiler_Pancake_SerializeFull_statusSeg(v_resp_115_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_srcS_116_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = lp_orb_x2dcompiler_Pancake_SerializeFull_headerSeg(v_resp_115_);
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v_srcH_117_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
lean_inc(v_body_119_);
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v_srcB_118_);
lean_ctor_set(v___x_124_, 1, v_body_119_);
v___x_125_ = lean_box(0);
v___x_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_123_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_121_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_respSegs___boxed(lean_object* v_resp_129_, lean_object* v_srcS_130_, lean_object* v_srcH_131_, lean_object* v_srcB_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = lp_orb_x2dcompiler_Pancake_SerializeFull_respSegs(v_resp_129_, v_srcS_130_, v_srcH_131_, v_srcB_132_);
lean_dec_ref(v_resp_129_);
return v_res_133_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_SerializeCompile(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_StructModel(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_SerializeFull(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_SerializeCompile(builtin);
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
