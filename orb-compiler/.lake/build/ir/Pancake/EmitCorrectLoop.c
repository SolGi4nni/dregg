// Lean compiler output
// Module: Pancake.EmitCorrectLoop
// Imports: public import Init public meta import Init public import Pancake.EmitCorrectCompose
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
static const lean_string_object lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "acc"};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__4;
static const lean_string_object lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "buf"};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__6_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "off"};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__7_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__7_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__6_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__9_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__10_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__10_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__11_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__9_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__12_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__12_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__13_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__14;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__15;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__16;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__17;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__18;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__3;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___lam__0___boxed(lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__5;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage(lean_object*);
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_unsigned_to_nat(31u);
v___x_5_ = lean_unsigned_to_nat(64u);
v___x_6_ = l_BitVec_ofNat(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__2, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__2);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__4(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__3, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__3);
v___x_10_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__1));
v___x_11_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
return v___x_11_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__14(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; lean_object* v___x_34_; 
v___x_31_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__13));
v___x_32_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__4, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__4);
v___x_33_ = 0;
v___x_34_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_34_, 0, v___x_32_);
lean_ctor_set(v___x_34_, 1, v___x_31_);
lean_ctor_set_uint8(v___x_34_, sizeof(void*)*2, v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__15(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_unsigned_to_nat(16777215u);
v___x_36_ = lean_unsigned_to_nat(64u);
v___x_37_ = l_BitVec_ofNat(v___x_36_, v___x_35_);
return v___x_37_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__16(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__15, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__15_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__15);
v___x_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
return v___x_39_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__17(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; lean_object* v___x_43_; 
v___x_40_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__16, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__16_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__16);
v___x_41_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__14, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__14_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__14);
v___x_42_ = 1;
v___x_43_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_43_, 0, v___x_41_);
lean_ctor_set(v___x_43_, 1, v___x_40_);
lean_ctor_set_uint8(v___x_43_, sizeof(void*)*2, v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__18(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__17, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__17_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__17);
v___x_45_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__0));
v___x_46_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set(v___x_46_, 1, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__18, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__18_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__18);
return v___x_47_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__0(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_unsigned_to_nat(1u);
v___x_49_ = lean_unsigned_to_nat(64u);
v___x_50_ = l_BitVec_ofNat(v___x_49_, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__1(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__0, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__0);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__2(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; lean_object* v___x_56_; 
v___x_53_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__1, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__1);
v___x_54_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__11));
v___x_55_ = 0;
v___x_56_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_56_, 0, v___x_54_);
lean_ctor_set(v___x_56_, 1, v___x_53_);
lean_ctor_set_uint8(v___x_56_, sizeof(void*)*2, v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__3(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__2, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__2);
v___x_58_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg___closed__10));
v___x_59_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg(void){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__3, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg___closed__3);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___lam__0(lean_object* v_s_61_){
_start:
{
lean_inc_ref(v_s_61_);
return v_s_61_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___lam__0___boxed(lean_object* v_s_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___lam__0(v_s_62_);
lean_dec_ref(v_s_62_);
return v_res_63_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__1(void){
_start:
{
lean_object* v___f_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___f_65_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__0));
v___x_66_ = lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg;
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___f_65_);
return v___x_67_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__2(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__1, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__1);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__3(void){
_start:
{
lean_object* v___f_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___f_70_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__0));
v___x_71_ = lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg;
v___x_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___f_70_);
return v___x_72_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__4(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__3, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__3);
v___x_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__5(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__4, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__4);
v___x_76_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__2, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__2);
v___x_77_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage(lean_object* v_00_u03c3_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__5, &lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyStage___closed__5);
return v___x_79_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_EmitCorrectCompose(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_EmitCorrectLoop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_EmitCorrectCompose(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg = _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyAccProg);
lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg = _init_lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_EmitCorrectLoop_scanBodyIProg);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
