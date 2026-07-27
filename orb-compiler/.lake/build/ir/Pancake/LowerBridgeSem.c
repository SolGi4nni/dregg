// Lean compiler output
// Module: Pancake.LowerBridgeSem
// Imports: public import Init public meta import Init public import Pancake.LowerBridge
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
lean_object* lp_orb_x2dcompiler_Pancake_wordSliceAlt(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_setWidth(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_byteAlign(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_setByte(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_getByteAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_getByteAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_setByteAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_setByteAt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_afterStore___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_afterStore___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_afterStore___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_afterStore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridgeSem_0__Pancake_LowerBridge_storesModel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridgeSem_0__Pancake_LowerBridge_storesModel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_getByteAt(lean_object* v_i_1_, lean_object* v_w_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_3_ = lean_unsigned_to_nat(64u);
v___x_4_ = lean_unsigned_to_nat(8u);
v___x_5_ = lean_nat_shiftr(v_w_2_, v_i_1_);
v___x_6_ = l_BitVec_setWidth(v___x_3_, v___x_4_, v___x_5_);
lean_dec(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_getByteAt___boxed(lean_object* v_i_7_, lean_object* v_w_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_orb_x2dcompiler_Pancake_LowerBridgeSem_getByteAt(v_i_7_, v_w_8_);
lean_dec(v_w_8_);
lean_dec(v_i_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_setByteAt(lean_object* v_i_10_, lean_object* v_b_11_, lean_object* v_w_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_13_ = lean_unsigned_to_nat(64u);
v___x_14_ = lean_unsigned_to_nat(8u);
v___x_15_ = lean_nat_add(v_i_10_, v___x_14_);
v___x_16_ = lp_orb_x2dcompiler_Pancake_wordSliceAlt(v___x_13_, v___x_15_, v_w_12_);
lean_dec(v___x_15_);
v___x_17_ = l_BitVec_setWidth(v___x_14_, v___x_13_, v_b_11_);
v___x_18_ = l_BitVec_shiftLeft(v___x_13_, v___x_17_, v_i_10_);
lean_dec(v___x_17_);
v___x_19_ = lean_nat_lor(v___x_16_, v___x_18_);
lean_dec(v___x_18_);
lean_dec(v___x_16_);
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lp_orb_x2dcompiler_Pancake_wordSliceAlt(v_i_10_, v___x_20_, v_w_12_);
v___x_22_ = lean_nat_lor(v___x_19_, v___x_21_);
lean_dec(v___x_21_);
lean_dec(v___x_19_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_setByteAt___boxed(lean_object* v_i_23_, lean_object* v_b_24_, lean_object* v_w_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_orb_x2dcompiler_Pancake_LowerBridgeSem_setByteAt(v_i_23_, v_b_24_, v_w_25_);
lean_dec(v_w_25_);
lean_dec(v_b_24_);
lean_dec(v_i_23_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_afterStore___redArg___lam__0(lean_object* v_adr_27_, lean_object* v_memory_28_, lean_object* v_bt_29_, uint8_t v_be_30_, lean_object* v_k_31_){
_start:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lp_orb_x2dcompiler_Pancake_byteAlign(v_adr_27_);
v___x_33_ = lean_nat_dec_eq(v_k_31_, v___x_32_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
lean_dec(v___x_32_);
v___x_34_ = lean_apply_1(v_memory_28_, v_k_31_);
return v___x_34_;
}
else
{
lean_object* v___x_35_; lean_object* v___x_36_; 
lean_dec(v_k_31_);
v___x_35_ = lean_apply_1(v_memory_28_, v___x_32_);
v___x_36_ = lp_orb_x2dcompiler_Pancake_setByte(v_adr_27_, v_bt_29_, v___x_35_, v_be_30_);
lean_dec(v___x_35_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_afterStore___redArg___lam__0___boxed(lean_object* v_adr_37_, lean_object* v_memory_38_, lean_object* v_bt_39_, lean_object* v_be_40_, lean_object* v_k_41_){
_start:
{
uint8_t v_be_boxed_42_; lean_object* v_res_43_; 
v_be_boxed_42_ = lean_unbox(v_be_40_);
v_res_43_ = lp_orb_x2dcompiler_Pancake_LowerBridgeSem_afterStore___redArg___lam__0(v_adr_37_, v_memory_38_, v_bt_39_, v_be_boxed_42_, v_k_41_);
lean_dec(v_bt_39_);
lean_dec(v_adr_37_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_afterStore___redArg(lean_object* v_s_44_, lean_object* v_adr_45_, lean_object* v_bt_46_){
_start:
{
lean_object* v_locals_47_; lean_object* v_memory_48_; lean_object* v_memaddrs_49_; uint8_t v_be_50_; lean_object* v_clock_51_; lean_object* v_ffi_52_; lean_object* v_baseAddr_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_62_; 
v_locals_47_ = lean_ctor_get(v_s_44_, 0);
v_memory_48_ = lean_ctor_get(v_s_44_, 1);
v_memaddrs_49_ = lean_ctor_get(v_s_44_, 2);
v_be_50_ = lean_ctor_get_uint8(v_s_44_, sizeof(void*)*6);
v_clock_51_ = lean_ctor_get(v_s_44_, 3);
v_ffi_52_ = lean_ctor_get(v_s_44_, 4);
v_baseAddr_53_ = lean_ctor_get(v_s_44_, 5);
v_isSharedCheck_62_ = !lean_is_exclusive(v_s_44_);
if (v_isSharedCheck_62_ == 0)
{
v___x_55_ = v_s_44_;
v_isShared_56_ = v_isSharedCheck_62_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_baseAddr_53_);
lean_inc(v_ffi_52_);
lean_inc(v_clock_51_);
lean_inc(v_memaddrs_49_);
lean_inc(v_memory_48_);
lean_inc(v_locals_47_);
lean_dec(v_s_44_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_62_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___f_58_; lean_object* v___x_60_; 
v___x_57_ = lean_box(v_be_50_);
v___f_58_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_LowerBridgeSem_afterStore___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_58_, 0, v_adr_45_);
lean_closure_set(v___f_58_, 1, v_memory_48_);
lean_closure_set(v___f_58_, 2, v_bt_46_);
lean_closure_set(v___f_58_, 3, v___x_57_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___f_58_);
v___x_60_ = v___x_55_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_locals_47_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v___f_58_);
lean_ctor_set(v_reuseFailAlloc_61_, 2, v_memaddrs_49_);
lean_ctor_set(v_reuseFailAlloc_61_, 3, v_clock_51_);
lean_ctor_set(v_reuseFailAlloc_61_, 4, v_ffi_52_);
lean_ctor_set(v_reuseFailAlloc_61_, 5, v_baseAddr_53_);
lean_ctor_set_uint8(v_reuseFailAlloc_61_, sizeof(void*)*6, v_be_50_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_LowerBridgeSem_afterStore(lean_object* v_00_u03c3_63_, lean_object* v_s_64_, lean_object* v_adr_65_, lean_object* v_bt_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lp_orb_x2dcompiler_Pancake_LowerBridgeSem_afterStore___redArg(v_s_64_, v_adr_65_, v_bt_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridgeSem_0__Pancake_LowerBridge_storesModel_match__1_splitter___redArg(lean_object* v_x_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_, lean_object* v_h__3_71_){
_start:
{
if (lean_obj_tag(v_x_68_) == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_h__3_71_);
lean_dec(v_h__2_70_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_apply_1(v_h__1_69_, v___x_72_);
return v___x_73_;
}
else
{
lean_object* v_tail_74_; 
lean_dec(v_h__1_69_);
v_tail_74_ = lean_ctor_get(v_x_68_, 1);
if (lean_obj_tag(v_tail_74_) == 0)
{
lean_object* v_head_75_; lean_object* v___x_76_; 
lean_dec(v_h__3_71_);
v_head_75_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_head_75_);
lean_dec_ref(v_x_68_);
v___x_76_ = lean_apply_1(v_h__2_70_, v_head_75_);
return v___x_76_;
}
else
{
lean_object* v_head_77_; lean_object* v___x_78_; 
lean_inc(v_tail_74_);
lean_dec(v_h__2_70_);
v_head_77_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_head_77_);
lean_dec_ref(v_x_68_);
v___x_78_ = lean_apply_3(v_h__3_71_, v_head_77_, v_tail_74_, lean_box(0));
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_LowerBridgeSem_0__Pancake_LowerBridge_storesModel_match__1_splitter(lean_object* v_motive_79_, lean_object* v_x_80_, lean_object* v_h__1_81_, lean_object* v_h__2_82_, lean_object* v_h__3_83_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_h__3_83_);
lean_dec(v_h__2_82_);
v___x_84_ = lean_box(0);
v___x_85_ = lean_apply_1(v_h__1_81_, v___x_84_);
return v___x_85_;
}
else
{
lean_object* v_tail_86_; 
lean_dec(v_h__1_81_);
v_tail_86_ = lean_ctor_get(v_x_80_, 1);
if (lean_obj_tag(v_tail_86_) == 0)
{
lean_object* v_head_87_; lean_object* v___x_88_; 
lean_dec(v_h__3_83_);
v_head_87_ = lean_ctor_get(v_x_80_, 0);
lean_inc(v_head_87_);
lean_dec_ref(v_x_80_);
v___x_88_ = lean_apply_1(v_h__2_82_, v_head_87_);
return v___x_88_;
}
else
{
lean_object* v_head_89_; lean_object* v___x_90_; 
lean_inc(v_tail_86_);
lean_dec(v_h__2_82_);
v_head_89_ = lean_ctor_get(v_x_80_, 0);
lean_inc(v_head_89_);
lean_dec_ref(v_x_80_);
v___x_90_ = lean_apply_3(v_h__3_83_, v_head_89_, v_tail_86_, lean_box(0));
return v___x_90_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_LowerBridge(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_LowerBridgeSem(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_LowerBridge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
