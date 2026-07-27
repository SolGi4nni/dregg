// Lean compiler output
// Module: Pancake.StatusLineEmit
// Imports: public import Init public meta import Init public import Pancake.NatToDecFull
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
extern lean_object* lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg;
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
extern lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
extern lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf;
lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_headerBlockOf(lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__2;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusTail(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusFieldProg;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__6;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__8;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__10;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__11;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__12;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__13;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__14;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__15;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__16;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__17;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__18;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__19;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__20;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__21;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__22;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404;
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_unsigned_to_nat(32u);
v___x_2_ = lean_unsigned_to_nat(8u);
v___x_3_ = l_BitVec_ofNat(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__0, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__0);
v___x_6_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__1, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__1);
v___x_8_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_http11;
v___x_9_ = l_List_appendTR___redArg(v___x_8_, v___x_7_);
return v___x_9_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__2, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__2);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusTail(lean_object* v_resp_11_){
_start:
{
lean_object* v_reason_12_; lean_object* v_body_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_reason_12_ = lean_ctor_get(v_resp_11_, 1);
v_body_13_ = lean_ctor_get(v_resp_11_, 3);
lean_inc(v_body_13_);
v___x_14_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__1, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__1);
lean_inc(v_reason_12_);
v___x_15_ = l_List_appendTR___redArg(v___x_14_, v_reason_12_);
v___x_16_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf;
v___x_17_ = l_List_appendTR___redArg(v___x_15_, v___x_16_);
v___x_18_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_headerBlockOf(v_resp_11_);
lean_dec_ref(v_resp_11_);
v___x_19_ = l_List_appendTR___redArg(v___x_17_, v___x_18_);
v___x_20_ = l_List_appendTR___redArg(v___x_19_, v___x_16_);
v___x_21_ = l_List_appendTR___redArg(v___x_20_, v___x_16_);
v___x_22_ = l_List_appendTR___redArg(v___x_21_, v_body_13_);
return v___x_22_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusFieldProg(void){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_orb_x2dcompiler_Pancake_NatToDecFull_natToDecProg;
return v___x_23_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__0(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_unsigned_to_nat(78u);
v___x_25_ = lean_unsigned_to_nat(8u);
v___x_26_ = l_BitVec_ofNat(v___x_25_, v___x_24_);
return v___x_26_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__1(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_unsigned_to_nat(111u);
v___x_28_ = lean_unsigned_to_nat(8u);
v___x_29_ = l_BitVec_ofNat(v___x_28_, v___x_27_);
return v___x_29_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__2(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_unsigned_to_nat(116u);
v___x_31_ = lean_unsigned_to_nat(8u);
v___x_32_ = l_BitVec_ofNat(v___x_31_, v___x_30_);
return v___x_32_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__3(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_unsigned_to_nat(70u);
v___x_34_ = lean_unsigned_to_nat(8u);
v___x_35_ = l_BitVec_ofNat(v___x_34_, v___x_33_);
return v___x_35_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__4(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_unsigned_to_nat(117u);
v___x_37_ = lean_unsigned_to_nat(8u);
v___x_38_ = l_BitVec_ofNat(v___x_37_, v___x_36_);
return v___x_38_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__5(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lean_unsigned_to_nat(110u);
v___x_40_ = lean_unsigned_to_nat(8u);
v___x_41_ = l_BitVec_ofNat(v___x_40_, v___x_39_);
return v___x_41_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__6(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = lean_unsigned_to_nat(100u);
v___x_43_ = lean_unsigned_to_nat(8u);
v___x_44_ = l_BitVec_ofNat(v___x_43_, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__7(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = lean_box(0);
v___x_46_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__6, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__6);
v___x_47_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_45_);
return v___x_47_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__8(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__7, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__7);
v___x_49_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__5, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__5);
v___x_50_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__9(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__8, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__8);
v___x_52_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__4, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__4);
v___x_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__10(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__9, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__9);
v___x_55_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__1, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__1);
v___x_56_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__11(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__10, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__10);
v___x_58_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__3, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__3);
v___x_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__12(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__11, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__11);
v___x_61_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__0, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix___closed__0);
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__13(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__12, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__12);
v___x_64_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__2, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__2);
v___x_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__14(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__13, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__13_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__13);
v___x_67_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__1, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__1);
v___x_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v___x_66_);
return v___x_68_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__15(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__14, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__14_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__14);
v___x_70_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__0, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__0);
v___x_71_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__16(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_unsigned_to_nat(112u);
v___x_73_ = lean_unsigned_to_nat(8u);
v___x_74_ = l_BitVec_ofNat(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__17(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_unsigned_to_nat(101u);
v___x_76_ = lean_unsigned_to_nat(8u);
v___x_77_ = l_BitVec_ofNat(v___x_76_, v___x_75_);
return v___x_77_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__18(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_box(0);
v___x_79_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__17, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__17_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__17);
v___x_80_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_78_);
return v___x_80_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__19(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__18, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__18_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__18);
v___x_82_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__16, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__16_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__16);
v___x_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__20(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__19, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__19_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__19);
v___x_85_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__1, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__1);
v___x_86_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__21(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__20, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__20_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__20);
v___x_88_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__5, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__5);
v___x_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__22(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_90_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__21, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__21_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__21);
v___x_91_ = lean_box(0);
v___x_92_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__15, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__15_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__15);
v___x_93_ = lean_unsigned_to_nat(404u);
v___x_94_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_92_);
lean_ctor_set(v___x_94_, 2, v___x_91_);
lean_ctor_set(v___x_94_, 3, v___x_90_);
return v___x_94_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404(void){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__22, &lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__22_once, _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404___closed__22);
return v___x_95_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_NatToDecFull(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_StatusLineEmit(uint8_t builtin) {
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
lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix = _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusPrefix);
lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusFieldProg = _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusFieldProg();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StatusLineEmit_statusFieldProg);
lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404 = _init_lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StatusLineEmit_resp404);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
