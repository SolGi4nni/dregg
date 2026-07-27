// Lean compiler output
// Module: Pancake.ByteCopy
// Imports: public import Init public meta import Init public import Pancake.NatToDecFull public import Pancake.EmitCorrectClock public import Pancake.EmitCorrectRegion
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
static const lean_string_object lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dst"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__1_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__4_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "src"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__6_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__7_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__7_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 9}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__4_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__9_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__10;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__11;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__12;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__13;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__14;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "len"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__3_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__3;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__2;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__10(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_unsigned_to_nat(64u);
v___x_25_ = l_BitVec_ofNat(v___x_24_, v___x_23_);
return v___x_25_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__11(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__10, &lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__10);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__12(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; lean_object* v___x_31_; 
v___x_28_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__11, &lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__11);
v___x_29_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__3));
v___x_30_ = 0;
v___x_31_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_31_, 0, v___x_29_);
lean_ctor_set(v___x_31_, 1, v___x_28_);
lean_ctor_set_uint8(v___x_31_, sizeof(void*)*2, v___x_30_);
return v___x_31_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__13(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__12, &lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__12);
v___x_33_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__2));
v___x_34_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v___x_32_);
return v___x_34_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__14(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__13, &lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__13_once, _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__13);
v___x_36_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__9));
v___x_37_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v___x_35_);
return v___x_37_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody(void){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__14, &lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__14_once, _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__14);
return v___x_38_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__3(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody;
v___x_47_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__2));
v___x_48_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__3, &lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__3);
return v___x_49_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__0(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_unsigned_to_nat(64u);
v___x_52_ = l_BitVec_ofNat(v___x_51_, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__1(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__0, &lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__0);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__2(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__1, &lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__1);
v___x_56_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__2));
v___x_57_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg(lean_object* v_dst_58_, lean_object* v_src_59_, lean_object* v_len_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_61_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__0));
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v_dst_58_);
v___x_63_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_61_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody___closed__5));
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v_src_59_);
v___x_66_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = lean_unsigned_to_nat(64u);
v___x_68_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__2, &lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___closed__2);
v___x_69_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile___closed__0));
v___x_70_ = l_BitVec_ofNat(v___x_67_, v_len_60_);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
v___x_72_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_69_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile;
v___x_74_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_72_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_68_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_66_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_63_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg___boxed(lean_object* v_dst_78_, lean_object* v_src_79_, lean_object* v_len_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg(v_dst_78_, v_src_79_, v_len_80_);
lean_dec(v_len_80_);
return v_res_81_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_NatToDecFull(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_EmitCorrectClock(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_EmitCorrectRegion(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_ByteCopy(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_NatToDecFull(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_EmitCorrectClock(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_EmitCorrectRegion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody = _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteBody);
lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile = _init_lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_ByteCopy_copyByteWhile);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
