// Lean compiler output
// Module: Pancake.NatToDecFull
// Imports: public import Init public meta import Init public import Pancake.NatToDecCompile public import Pancake.BytesModel
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divWhile;
static const lean_string_object lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "q"};
static const lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__3;
static const lean_string_object lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__4_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__5_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__6;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__8;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__9;
static const lean_string_object lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__10_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__10_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__11_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__12;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__13;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__14;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__15;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__16 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__16_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__10_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__16_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__17 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__17_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__18;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__19;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__20;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__21;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitFuelAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitFuelAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitFuel(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitFuel___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_natFuel(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_natFuel___boxed(lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg;
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = lean_unsigned_to_nat(64u);
v___x_4_ = l_BitVec_ofNat(v___x_3_, v___x_2_);
return v___x_4_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__1, &lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__1);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__2, &lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__2);
v___x_8_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__0));
v___x_9_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_7_);
return v___x_9_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__6(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_13_ = lean_unsigned_to_nat(1u);
v___x_14_ = lean_unsigned_to_nat(64u);
v___x_15_ = l_BitVec_ofNat(v___x_14_, v___x_13_);
return v___x_15_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__7(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__6, &lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__6);
v___x_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__8(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; lean_object* v___x_21_; 
v___x_18_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__7, &lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__7);
v___x_19_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__5));
v___x_20_ = 2;
v___x_21_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_21_, 0, v___x_19_);
lean_ctor_set(v___x_21_, 1, v___x_18_);
lean_ctor_set_uint8(v___x_21_, sizeof(void*)*2, v___x_20_);
return v___x_21_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__9(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__8, &lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__8);
v___x_23_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__4));
v___x_24_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v___x_22_);
return v___x_24_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__12(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_unsigned_to_nat(48u);
v___x_29_ = lean_unsigned_to_nat(64u);
v___x_30_ = l_BitVec_ofNat(v___x_29_, v___x_28_);
return v___x_30_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__13(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__12, &lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__12);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__14(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; lean_object* v___x_36_; 
v___x_33_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__13, &lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__13_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__13);
v___x_34_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__11));
v___x_35_ = 0;
v___x_36_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_36_, 0, v___x_34_);
lean_ctor_set(v___x_36_, 1, v___x_33_);
lean_ctor_set_uint8(v___x_36_, sizeof(void*)*2, v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__15(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__14, &lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__14_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__14);
v___x_38_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__5));
v___x_39_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__18(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__17));
v___x_46_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__15, &lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__15_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__15);
v___x_47_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_45_);
return v___x_47_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__19(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__18, &lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__18_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__18);
v___x_49_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__9, &lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__9);
v___x_50_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__20(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__19, &lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__19_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__19);
v___x_52_ = lp_orb_x2dcompiler_Pancake_NatToDecCompile_divWhile;
v___x_53_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__21(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__20, &lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__20_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__20);
v___x_55_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__3, &lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__3);
v___x_56_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__21, &lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__21_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__21);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitFuelAux(lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_zero_60_; uint8_t v_isZero_61_; 
v_zero_60_ = lean_unsigned_to_nat(0u);
v_isZero_61_ = lean_nat_dec_eq(v_x_58_, v_zero_60_);
if (v_isZero_61_ == 1)
{
lean_object* v___x_62_; 
v___x_62_ = lean_unsigned_to_nat(1u);
return v___x_62_;
}
else
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = lean_unsigned_to_nat(10u);
v___x_64_ = lean_nat_dec_lt(v_x_59_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v_one_65_; lean_object* v_n_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_one_65_ = lean_unsigned_to_nat(1u);
v_n_66_ = lean_nat_sub(v_x_58_, v_one_65_);
v___x_67_ = lean_nat_div(v_x_59_, v___x_63_);
v___x_68_ = lean_nat_add(v_one_65_, v___x_67_);
v___x_69_ = lp_orb_x2dcompiler_Pancake_NatToDecFull_digitFuelAux(v_n_66_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v_n_66_);
v___x_70_ = lean_nat_add(v___x_68_, v___x_69_);
lean_dec(v___x_69_);
lean_dec(v___x_68_);
return v___x_70_;
}
else
{
lean_object* v___x_71_; 
v___x_71_ = lean_unsigned_to_nat(1u);
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitFuelAux___boxed(lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = lp_orb_x2dcompiler_Pancake_NatToDecFull_digitFuelAux(v_x_72_, v_x_73_);
lean_dec(v_x_73_);
lean_dec(v_x_72_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitFuel(lean_object* v_m_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lp_orb_x2dcompiler_Pancake_NatToDecFull_digitFuelAux(v_m_75_, v_m_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_digitFuel___boxed(lean_object* v_m_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = lp_orb_x2dcompiler_Pancake_NatToDecFull_digitFuel(v_m_77_);
lean_dec(v_m_77_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_natFuel(lean_object* v_m_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_80_ = lean_unsigned_to_nat(10u);
v___x_81_ = lean_nat_div(v_m_79_, v___x_80_);
v___x_82_ = lean_unsigned_to_nat(0u);
v___x_83_ = lean_nat_dec_eq(v___x_81_, v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lp_orb_x2dcompiler_Pancake_NatToDecFull_digitFuelAux(v___x_81_, v___x_81_);
v___x_85_ = lean_nat_add(v___x_81_, v___x_84_);
lean_dec(v___x_84_);
lean_dec(v___x_81_);
return v___x_85_;
}
else
{
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_natFuel___boxed(lean_object* v_m_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_orb_x2dcompiler_Pancake_NatToDecFull_natFuel(v_m_86_);
lean_dec(v_m_86_);
return v_res_87_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg___closed__0(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody;
v___x_89_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody___closed__11));
v___x_90_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg___closed__1(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg___closed__0, &lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg___closed__0);
v___x_92_ = lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody;
v___x_93_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg(void){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg___closed__1, &lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg___closed__1);
return v___x_94_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_NatToDecCompile(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_BytesModel(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_NatToDecFull(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_NatToDecCompile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_BytesModel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody = _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_NatToDecFull_digitBody);
lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg = _init_lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
