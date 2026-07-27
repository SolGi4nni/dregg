// Lean compiler output
// Module: Pancake.NatToDecCompile
// Imports: public import Init public meta import Init public import Pancake.SerializeCompile
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
static const lean_string_object lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "q"};
static const lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__3_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__6;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__8;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_NatToDecCompile_divWhile___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divWhile___closed__0;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_NatToDecCompile_divWhile;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_NatToDecCompile_0__Pancake_eval_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_NatToDecCompile_0__Pancake_eval_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_unsigned_to_nat(10u);
v___x_5_ = lean_unsigned_to_nat(64u);
v___x_6_ = l_BitVec_ofNat(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__2, &lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__2);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__4(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; 
v___x_9_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__3, &lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__3);
v___x_10_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__1));
v___x_11_ = 2;
v___x_12_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_12_, 0, v___x_10_);
lean_ctor_set(v___x_12_, 1, v___x_9_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*2, v___x_11_);
return v___x_12_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__4, &lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__4);
return v___x_13_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__0(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; lean_object* v___x_17_; 
v___x_14_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__3, &lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__3);
v___x_15_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__1));
v___x_16_ = 2;
v___x_17_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_17_, 0, v___x_15_);
lean_ctor_set(v___x_17_, 1, v___x_14_);
lean_ctor_set_uint8(v___x_17_, sizeof(void*)*2, v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__1(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_18_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__0, &lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__0);
v___x_19_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard___closed__0));
v___x_20_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___x_18_);
return v___x_20_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__4(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = lean_unsigned_to_nat(64u);
v___x_26_ = l_BitVec_ofNat(v___x_25_, v___x_24_);
return v___x_26_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__5(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__4, &lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__4);
v___x_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__6(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; lean_object* v___x_32_; 
v___x_29_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__5, &lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__5);
v___x_30_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__3));
v___x_31_ = 0;
v___x_32_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_32_, 0, v___x_30_);
lean_ctor_set(v___x_32_, 1, v___x_29_);
lean_ctor_set_uint8(v___x_32_, sizeof(void*)*2, v___x_31_);
return v___x_32_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__7(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__6, &lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__6);
v___x_34_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__2));
v___x_35_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_33_);
return v___x_35_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__8(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__7, &lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__7);
v___x_37_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__1, &lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__1);
v___x_38_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
return v___x_38_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__8, &lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody___closed__8);
return v___x_39_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divWhile___closed__0(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody;
v___x_41_ = lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard;
v___x_42_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_40_);
return v___x_42_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divWhile(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_NatToDecCompile_divWhile___closed__0, &lp_orb_x2dcompiler_Pancake_NatToDecCompile_divWhile___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divWhile___closed__0);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_NatToDecCompile_0__Pancake_eval_match__1_splitter___redArg(lean_object* v_x_44_, lean_object* v_x_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
if (lean_obj_tag(v_x_44_) == 1)
{
if (lean_obj_tag(v_x_45_) == 1)
{
lean_object* v_val_48_; lean_object* v_val_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_47_);
v_val_48_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_val_48_);
lean_dec_ref(v_x_44_);
v_val_49_ = lean_ctor_get(v_x_45_, 0);
lean_inc(v_val_49_);
lean_dec_ref(v_x_45_);
v___x_50_ = lean_apply_2(v_h__1_46_, v_val_48_, v_val_49_);
return v___x_50_;
}
else
{
lean_object* v___x_51_; 
lean_dec(v_h__1_46_);
v___x_51_ = lean_apply_3(v_h__2_47_, v_x_44_, v_x_45_, lean_box(0));
return v___x_51_;
}
}
else
{
lean_object* v___x_52_; 
lean_dec(v_h__1_46_);
v___x_52_ = lean_apply_3(v_h__2_47_, v_x_44_, v_x_45_, lean_box(0));
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_NatToDecCompile_0__Pancake_eval_match__1_splitter(lean_object* v_motive_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_){
_start:
{
if (lean_obj_tag(v_x_54_) == 1)
{
if (lean_obj_tag(v_x_55_) == 1)
{
lean_object* v_val_58_; lean_object* v_val_59_; lean_object* v___x_60_; 
lean_dec(v_h__2_57_);
v_val_58_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_val_58_);
lean_dec_ref(v_x_54_);
v_val_59_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_val_59_);
lean_dec_ref(v_x_55_);
v___x_60_ = lean_apply_2(v_h__1_56_, v_val_58_, v_val_59_);
return v___x_60_;
}
else
{
lean_object* v___x_61_; 
lean_dec(v_h__1_56_);
v___x_61_ = lean_apply_3(v_h__2_57_, v_x_54_, v_x_55_, lean_box(0));
return v___x_61_;
}
}
else
{
lean_object* v___x_62_; 
lean_dec(v_h__1_56_);
v___x_62_ = lean_apply_3(v_h__2_57_, v_x_54_, v_x_55_, lean_box(0));
return v___x_62_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_SerializeCompile(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_NatToDecCompile(uint8_t builtin) {
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
lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard = _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_NatToDecCompile_divGuard);
lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody = _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_NatToDecCompile_divBody);
lp_orb_x2dcompiler_Pancake_NatToDecCompile_divWhile = _init_lp_orb_x2dcompiler_Pancake_NatToDecCompile_divWhile();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_NatToDecCompile_divWhile);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
