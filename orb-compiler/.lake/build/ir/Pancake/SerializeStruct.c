// Lean compiler output
// Module: Pancake.SerializeStruct
// Imports: public import Init public meta import Init public import Pancake.SerializeHeaders
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
extern lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLineOf(lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_headerBlockOf(lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_statusSeg(lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_build(lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_allHeaders(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_SerializeHeaders_segOf(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_withPtrs___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_withPtrs___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_withPtrs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_bodySeg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_SerializeStruct_fullSegProj_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_fullSegProj(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_fullSegs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_headBytes(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_headBytes___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_withPtrs___lam__0(lean_object* v_ptr_1_, lean_object* v_k_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_add(v_k_2_, v___x_3_);
v___x_5_ = lean_apply_1(v_ptr_1_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_withPtrs___lam__0___boxed(lean_object* v_ptr_6_, lean_object* v_k_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_orb_x2dcompiler_Pancake_SerializeStruct_withPtrs___lam__0(v_ptr_6_, v_k_7_);
lean_dec(v_k_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_withPtrs(lean_object* v_ptr_9_, lean_object* v_x_10_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_11_; 
lean_dec_ref(v_ptr_9_);
v___x_11_ = lean_box(0);
return v___x_11_;
}
else
{
lean_object* v_head_12_; lean_object* v_tail_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_25_; 
v_head_12_ = lean_ctor_get(v_x_10_, 0);
v_tail_13_ = lean_ctor_get(v_x_10_, 1);
v_isSharedCheck_25_ = !lean_is_exclusive(v_x_10_);
if (v_isSharedCheck_25_ == 0)
{
v___x_15_ = v_x_10_;
v_isShared_16_ = v_isSharedCheck_25_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_tail_13_);
lean_inc(v_head_12_);
lean_dec(v_x_10_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_25_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___f_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_23_; 
lean_inc_ref(v_ptr_9_);
v___f_17_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_SerializeStruct_withPtrs___lam__0___boxed), 2, 1);
lean_closure_set(v___f_17_, 0, v_ptr_9_);
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_apply_1(v_ptr_9_, v___x_18_);
v___x_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v_head_12_);
v___x_21_ = lp_orb_x2dcompiler_Pancake_SerializeStruct_withPtrs(v___f_17_, v_tail_13_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 1, v___x_21_);
lean_ctor_set(v___x_15_, 0, v___x_20_);
v___x_23_ = v___x_15_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_20_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v___x_21_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_bodySeg(lean_object* v_resp_26_){
_start:
{
lean_object* v_body_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v_body_27_ = lean_ctor_get(v_resp_26_, 3);
lean_inc(v_body_27_);
lean_dec_ref(v_resp_26_);
v___x_28_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf;
v___x_29_ = l_List_appendTR___redArg(v___x_28_, v_body_27_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_SerializeStruct_fullSegProj_spec__0(lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
if (lean_obj_tag(v_a_30_) == 0)
{
lean_object* v___x_32_; 
v___x_32_ = l_List_reverse___redArg(v_a_31_);
return v___x_32_;
}
else
{
lean_object* v_head_33_; lean_object* v_tail_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_43_; 
v_head_33_ = lean_ctor_get(v_a_30_, 0);
v_tail_34_ = lean_ctor_get(v_a_30_, 1);
v_isSharedCheck_43_ = !lean_is_exclusive(v_a_30_);
if (v_isSharedCheck_43_ == 0)
{
v___x_36_ = v_a_30_;
v_isShared_37_ = v_isSharedCheck_43_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_tail_34_);
lean_inc(v_head_33_);
lean_dec(v_a_30_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_43_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_38_ = lp_orb_x2dcompiler_Pancake_SerializeHeaders_segOf(v_head_33_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 1, v_a_31_);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v_a_31_);
v___x_40_ = v_reuseFailAlloc_42_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
v_a_30_ = v_tail_34_;
v_a_31_ = v___x_40_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_fullSegProj(lean_object* v_resp_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_45_ = lp_orb_x2dcompiler_Pancake_SerializeFull_statusSeg(v_resp_44_);
v___x_46_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_build(v_resp_44_);
v___x_47_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_allHeaders(v___x_46_);
v___x_48_ = lean_box(0);
v___x_49_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_SerializeStruct_fullSegProj_spec__0(v___x_47_, v___x_48_);
v___x_50_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_45_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
v___x_51_ = lp_orb_x2dcompiler_Pancake_SerializeStruct_bodySeg(v_resp_44_);
v___x_52_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_48_);
v___x_53_ = l_List_appendTR___redArg(v___x_50_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_fullSegs(lean_object* v_resp_54_, lean_object* v_ptr_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lp_orb_x2dcompiler_Pancake_SerializeStruct_fullSegProj(v_resp_54_);
v___x_57_ = lp_orb_x2dcompiler_Pancake_SerializeStruct_withPtrs(v_ptr_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_headBytes(lean_object* v_resp_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_59_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLineOf(v_resp_58_);
v___x_60_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf;
v___x_61_ = l_List_appendTR___redArg(v___x_59_, v___x_60_);
v___x_62_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_headerBlockOf(v_resp_58_);
v___x_63_ = l_List_appendTR___redArg(v___x_61_, v___x_62_);
v___x_64_ = l_List_appendTR___redArg(v___x_63_, v___x_60_);
v___x_65_ = l_List_appendTR___redArg(v___x_64_, v___x_60_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_headBytes___boxed(lean_object* v_resp_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_orb_x2dcompiler_Pancake_SerializeStruct_headBytes(v_resp_66_);
lean_dec_ref(v_resp_66_);
return v_res_67_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_SerializeHeaders(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_SerializeStruct(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_SerializeHeaders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
