// Lean compiler output
// Module: Pancake.BytesModel
// Imports: public import Init public meta import Init public import Pancake.Sem
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
lean_object* lp_orb_x2dcompiler_Pancake_byteAlign(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_setByte(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_BytesModel_putByte(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_BytesModel_putByte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_BytesModel_0__Pancake_writeByteArray_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_BytesModel_0__Pancake_writeByteArray_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_BytesModel_0__Pancake_writeByteArray_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_BytesModel_0__Pancake_writeByteArray_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_BytesModel_putByte(lean_object* v_m_1_, uint8_t v_be_2_, lean_object* v_w_3_, lean_object* v_b_4_, lean_object* v_k_5_){
_start:
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = lp_orb_x2dcompiler_Pancake_byteAlign(v_w_3_);
v___x_7_ = lean_nat_dec_eq(v_k_5_, v___x_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; 
lean_dec(v___x_6_);
v___x_8_ = lean_apply_1(v_m_1_, v_k_5_);
return v___x_8_;
}
else
{
lean_object* v___x_9_; lean_object* v___x_10_; 
lean_dec(v_k_5_);
v___x_9_ = lean_apply_1(v_m_1_, v___x_6_);
v___x_10_ = lp_orb_x2dcompiler_Pancake_setByte(v_w_3_, v_b_4_, v___x_9_, v_be_2_);
lean_dec(v___x_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_BytesModel_putByte___boxed(lean_object* v_m_11_, lean_object* v_be_12_, lean_object* v_w_13_, lean_object* v_b_14_, lean_object* v_k_15_){
_start:
{
uint8_t v_be_boxed_16_; lean_object* v_res_17_; 
v_be_boxed_16_ = lean_unbox(v_be_12_);
v_res_17_ = lp_orb_x2dcompiler_Pancake_BytesModel_putByte(v_m_11_, v_be_boxed_16_, v_w_13_, v_b_14_, v_k_15_);
lean_dec(v_b_14_);
lean_dec(v_w_13_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_BytesModel_0__Pancake_writeByteArray_match__3_splitter___redArg(lean_object* v_x_18_, lean_object* v_x_19_, lean_object* v_x_20_, lean_object* v_h__1_21_, lean_object* v_h__2_22_){
_start:
{
if (lean_obj_tag(v_x_19_) == 0)
{
lean_object* v___x_23_; 
lean_dec(v_h__2_22_);
v___x_23_ = lean_apply_2(v_h__1_21_, v_x_18_, v_x_20_);
return v___x_23_;
}
else
{
lean_object* v_head_24_; lean_object* v_tail_25_; lean_object* v___x_26_; 
lean_dec(v_h__1_21_);
v_head_24_ = lean_ctor_get(v_x_19_, 0);
lean_inc(v_head_24_);
v_tail_25_ = lean_ctor_get(v_x_19_, 1);
lean_inc(v_tail_25_);
lean_dec_ref(v_x_19_);
v___x_26_ = lean_apply_4(v_h__2_22_, v_x_18_, v_head_24_, v_tail_25_, v_x_20_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_BytesModel_0__Pancake_writeByteArray_match__3_splitter(lean_object* v_motive_27_, lean_object* v_x_28_, lean_object* v_x_29_, lean_object* v_x_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_){
_start:
{
if (lean_obj_tag(v_x_29_) == 0)
{
lean_object* v___x_33_; 
lean_dec(v_h__2_32_);
v___x_33_ = lean_apply_2(v_h__1_31_, v_x_28_, v_x_30_);
return v___x_33_;
}
else
{
lean_object* v_head_34_; lean_object* v_tail_35_; lean_object* v___x_36_; 
lean_dec(v_h__1_31_);
v_head_34_ = lean_ctor_get(v_x_29_, 0);
lean_inc(v_head_34_);
v_tail_35_ = lean_ctor_get(v_x_29_, 1);
lean_inc(v_tail_35_);
lean_dec_ref(v_x_29_);
v___x_36_ = lean_apply_4(v_h__2_32_, v_x_28_, v_head_34_, v_tail_35_, v_x_30_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_BytesModel_0__Pancake_writeByteArray_match__1_splitter___redArg(lean_object* v_x_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_h__1_38_);
v___x_40_ = lean_box(0);
v___x_41_ = lean_apply_1(v_h__2_39_, v___x_40_);
return v___x_41_;
}
else
{
lean_object* v_val_42_; lean_object* v___x_43_; 
lean_dec(v_h__2_39_);
v_val_42_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_val_42_);
lean_dec_ref(v_x_37_);
v___x_43_ = lean_apply_1(v_h__1_38_, v_val_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_BytesModel_0__Pancake_writeByteArray_match__1_splitter(lean_object* v_motive_44_, lean_object* v_x_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
if (lean_obj_tag(v_x_45_) == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_h__1_46_);
v___x_48_ = lean_box(0);
v___x_49_ = lean_apply_1(v_h__2_47_, v___x_48_);
return v___x_49_;
}
else
{
lean_object* v_val_50_; lean_object* v___x_51_; 
lean_dec(v_h__2_47_);
v_val_50_ = lean_ctor_get(v_x_45_, 0);
lean_inc(v_val_50_);
lean_dec_ref(v_x_45_);
v___x_51_ = lean_apply_1(v_h__1_46_, v_val_50_);
return v___x_51_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_Sem(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_BytesModel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_Sem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
