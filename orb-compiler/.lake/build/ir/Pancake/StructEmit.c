// Lean compiler output
// Module: Pancake.StructEmit
// Imports: public import Init public meta import Init public import Pancake.SerializeStruct
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
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_wordOfByte(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_headBytes(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeLitByte(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeLitByte___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeLitFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeLitFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeLit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeCount(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeCount___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_StructEmit_0__Pancake_StructEmit_storeCount_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_StructEmit_0__Pancake_StructEmit_storeCount_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_respEmit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_respEmit___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__6;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__8;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__10;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__11;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__12;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__13;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__14;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__15;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__16;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__17;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__18;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__19;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__20;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__21;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__22;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__23;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__6;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__8;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_wmem(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_wmem___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___closed__0_value;
static const lean_closure_object lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___closed__1_value;
static const lean_closure_object lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_StructEmit_wmem___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___closed__2_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_witnessState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeLitByte(lean_object* v_base_1_, lean_object* v_off_2_, lean_object* v_b_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_4_ = lean_unsigned_to_nat(64u);
v___x_5_ = l_BitVec_ofNat(v___x_4_, v_off_2_);
v___x_6_ = l_BitVec_add(v___x_4_, v_base_1_, v___x_5_);
lean_dec(v___x_5_);
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
v___x_8_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_wordOfByte(v_b_3_);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
v___x_10_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_7_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeLitByte___boxed(lean_object* v_base_11_, lean_object* v_off_12_, lean_object* v_b_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_orb_x2dcompiler_Pancake_StructEmit_storeLitByte(v_base_11_, v_off_12_, v_b_13_);
lean_dec(v_b_13_);
lean_dec(v_off_12_);
lean_dec(v_base_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeLitFrom(lean_object* v_base_15_, lean_object* v_off_16_, lean_object* v_x_17_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
else
{
lean_object* v_head_19_; lean_object* v_tail_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_31_; 
v_head_19_ = lean_ctor_get(v_x_17_, 0);
v_tail_20_ = lean_ctor_get(v_x_17_, 1);
v_isSharedCheck_31_ = !lean_is_exclusive(v_x_17_);
if (v_isSharedCheck_31_ == 0)
{
v___x_22_ = v_x_17_;
v_isShared_23_ = v_isSharedCheck_31_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_tail_20_);
lean_inc(v_head_19_);
lean_dec(v_x_17_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_31_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_29_; 
v___x_24_ = lp_orb_x2dcompiler_Pancake_StructEmit_storeLitByte(v_base_15_, v_off_16_, v_head_19_);
lean_dec(v_head_19_);
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = lean_nat_add(v_off_16_, v___x_25_);
v___x_27_ = lp_orb_x2dcompiler_Pancake_StructEmit_storeLitFrom(v_base_15_, v___x_26_, v_tail_20_);
lean_dec(v___x_26_);
if (v_isShared_23_ == 0)
{
lean_ctor_set_tag(v___x_22_, 5);
lean_ctor_set(v___x_22_, 1, v___x_27_);
lean_ctor_set(v___x_22_, 0, v___x_24_);
v___x_29_ = v___x_22_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v___x_27_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeLitFrom___boxed(lean_object* v_base_32_, lean_object* v_off_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_orb_x2dcompiler_Pancake_StructEmit_storeLitFrom(v_base_32_, v_off_33_, v_x_34_);
lean_dec(v_off_33_);
lean_dec(v_base_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeLit(lean_object* v_base_36_, lean_object* v_bs_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_unsigned_to_nat(0u);
v___x_39_ = lp_orb_x2dcompiler_Pancake_StructEmit_storeLitFrom(v_base_36_, v___x_38_, v_bs_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeLit___boxed(lean_object* v_base_40_, lean_object* v_bs_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_orb_x2dcompiler_Pancake_StructEmit_storeLit(v_base_40_, v_bs_41_);
lean_dec(v_base_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeCount(lean_object* v_x_43_){
_start:
{
switch(lean_obj_tag(v_x_43_))
{
case 0:
{
lean_object* v___x_44_; 
v___x_44_ = lean_unsigned_to_nat(0u);
return v___x_44_;
}
case 3:
{
lean_object* v___x_45_; 
v___x_45_ = lean_unsigned_to_nat(1u);
return v___x_45_;
}
case 5:
{
lean_object* v_c1_46_; lean_object* v_c2_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_c1_46_ = lean_ctor_get(v_x_43_, 0);
v_c2_47_ = lean_ctor_get(v_x_43_, 1);
v___x_48_ = lp_orb_x2dcompiler_Pancake_StructEmit_storeCount(v_c1_46_);
v___x_49_ = lp_orb_x2dcompiler_Pancake_StructEmit_storeCount(v_c2_47_);
v___x_50_ = lean_nat_add(v___x_48_, v___x_49_);
lean_dec(v___x_49_);
lean_dec(v___x_48_);
return v___x_50_;
}
default: 
{
lean_object* v___x_51_; 
v___x_51_ = lean_unsigned_to_nat(0u);
return v___x_51_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_storeCount___boxed(lean_object* v_x_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = lp_orb_x2dcompiler_Pancake_StructEmit_storeCount(v_x_52_);
lean_dec(v_x_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_StructEmit_0__Pancake_StructEmit_storeCount_match__1_splitter___redArg(lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_, lean_object* v_h__3_57_, lean_object* v_h__4_58_){
_start:
{
switch(lean_obj_tag(v_x_54_))
{
case 0:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_h__4_58_);
lean_dec(v_h__3_57_);
lean_dec(v_h__2_56_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_apply_1(v_h__1_55_, v___x_59_);
return v___x_60_;
}
case 3:
{
lean_object* v_dst_61_; lean_object* v_src_62_; lean_object* v___x_63_; 
lean_dec(v_h__4_58_);
lean_dec(v_h__3_57_);
lean_dec(v_h__1_55_);
v_dst_61_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_dst_61_);
v_src_62_ = lean_ctor_get(v_x_54_, 1);
lean_inc(v_src_62_);
lean_dec_ref(v_x_54_);
v___x_63_ = lean_apply_2(v_h__2_56_, v_dst_61_, v_src_62_);
return v___x_63_;
}
case 5:
{
lean_object* v_c1_64_; lean_object* v_c2_65_; lean_object* v___x_66_; 
lean_dec(v_h__4_58_);
lean_dec(v_h__2_56_);
lean_dec(v_h__1_55_);
v_c1_64_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_c1_64_);
v_c2_65_ = lean_ctor_get(v_x_54_, 1);
lean_inc(v_c2_65_);
lean_dec_ref(v_x_54_);
v___x_66_ = lean_apply_2(v_h__3_57_, v_c1_64_, v_c2_65_);
return v___x_66_;
}
default: 
{
lean_object* v___x_67_; 
lean_dec(v_h__3_57_);
lean_dec(v_h__2_56_);
lean_dec(v_h__1_55_);
v___x_67_ = lean_apply_4(v_h__4_58_, v_x_54_, lean_box(0), lean_box(0), lean_box(0));
return v___x_67_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_StructEmit_0__Pancake_StructEmit_storeCount_match__1_splitter(lean_object* v_motive_68_, lean_object* v_x_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_, lean_object* v_h__3_72_, lean_object* v_h__4_73_){
_start:
{
switch(lean_obj_tag(v_x_69_))
{
case 0:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v_h__4_73_);
lean_dec(v_h__3_72_);
lean_dec(v_h__2_71_);
v___x_74_ = lean_box(0);
v___x_75_ = lean_apply_1(v_h__1_70_, v___x_74_);
return v___x_75_;
}
case 3:
{
lean_object* v_dst_76_; lean_object* v_src_77_; lean_object* v___x_78_; 
lean_dec(v_h__4_73_);
lean_dec(v_h__3_72_);
lean_dec(v_h__1_70_);
v_dst_76_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_dst_76_);
v_src_77_ = lean_ctor_get(v_x_69_, 1);
lean_inc(v_src_77_);
lean_dec_ref(v_x_69_);
v___x_78_ = lean_apply_2(v_h__2_71_, v_dst_76_, v_src_77_);
return v___x_78_;
}
case 5:
{
lean_object* v_c1_79_; lean_object* v_c2_80_; lean_object* v___x_81_; 
lean_dec(v_h__4_73_);
lean_dec(v_h__2_71_);
lean_dec(v_h__1_70_);
v_c1_79_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_c1_79_);
v_c2_80_ = lean_ctor_get(v_x_69_, 1);
lean_inc(v_c2_80_);
lean_dec_ref(v_x_69_);
v___x_81_ = lean_apply_2(v_h__3_72_, v_c1_79_, v_c2_80_);
return v___x_81_;
}
default: 
{
lean_object* v___x_82_; 
lean_dec(v_h__3_72_);
lean_dec(v_h__2_71_);
lean_dec(v_h__1_70_);
v___x_82_ = lean_apply_4(v_h__4_73_, v_x_69_, lean_box(0), lean_box(0), lean_box(0));
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_respEmit(lean_object* v_resp_83_, lean_object* v_obase_84_, lean_object* v_src_85_){
_start:
{
lean_object* v_body_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_body_86_ = lean_ctor_get(v_resp_83_, 3);
v___x_87_ = lp_orb_x2dcompiler_Pancake_SerializeStruct_headBytes(v_resp_83_);
lean_inc(v___x_87_);
v___x_88_ = lp_orb_x2dcompiler_Pancake_StructEmit_storeLit(v_obase_84_, v___x_87_);
v___x_89_ = l_List_lengthTR___redArg(v___x_87_);
lean_dec(v___x_87_);
v___x_90_ = l_List_lengthTR___redArg(v_body_86_);
v___x_91_ = lp_orb_x2dcompiler_Pancake_SerializeFull_writeSeg(v_obase_84_, v___x_89_, v_src_85_, v___x_90_);
lean_dec(v___x_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_88_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_respEmit___boxed(lean_object* v_resp_93_, lean_object* v_obase_94_, lean_object* v_src_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = lp_orb_x2dcompiler_Pancake_StructEmit_respEmit(v_resp_93_, v_obase_94_, v_src_95_);
lean_dec(v_obase_94_);
lean_dec_ref(v_resp_93_);
return v_res_96_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__0(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_unsigned_to_nat(78u);
v___x_98_ = lean_unsigned_to_nat(8u);
v___x_99_ = l_BitVec_ofNat(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__1(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_unsigned_to_nat(111u);
v___x_101_ = lean_unsigned_to_nat(8u);
v___x_102_ = l_BitVec_ofNat(v___x_101_, v___x_100_);
return v___x_102_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__2(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_unsigned_to_nat(116u);
v___x_104_ = lean_unsigned_to_nat(8u);
v___x_105_ = l_BitVec_ofNat(v___x_104_, v___x_103_);
return v___x_105_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__3(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_unsigned_to_nat(32u);
v___x_107_ = lean_unsigned_to_nat(8u);
v___x_108_ = l_BitVec_ofNat(v___x_107_, v___x_106_);
return v___x_108_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__4(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_unsigned_to_nat(70u);
v___x_110_ = lean_unsigned_to_nat(8u);
v___x_111_ = l_BitVec_ofNat(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__5(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = lean_unsigned_to_nat(117u);
v___x_113_ = lean_unsigned_to_nat(8u);
v___x_114_ = l_BitVec_ofNat(v___x_113_, v___x_112_);
return v___x_114_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__6(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_unsigned_to_nat(110u);
v___x_116_ = lean_unsigned_to_nat(8u);
v___x_117_ = l_BitVec_ofNat(v___x_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__7(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = lean_unsigned_to_nat(100u);
v___x_119_ = lean_unsigned_to_nat(8u);
v___x_120_ = l_BitVec_ofNat(v___x_119_, v___x_118_);
return v___x_120_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__8(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_box(0);
v___x_122_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__7, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__7);
v___x_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
return v___x_123_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__9(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__8, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__8);
v___x_125_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__6, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__6);
v___x_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_124_);
return v___x_126_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__10(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__9, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__9);
v___x_128_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__5, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__5);
v___x_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
return v___x_129_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__11(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__10, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__10);
v___x_131_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__1, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__1);
v___x_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
return v___x_132_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__12(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__11, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__11);
v___x_134_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__4, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__4);
v___x_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__13(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__12, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__12);
v___x_137_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__3, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__3);
v___x_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
return v___x_138_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__14(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__13, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__13_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__13);
v___x_140_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__2, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__2);
v___x_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__15(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__14, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__14_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__14);
v___x_143_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__1, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__1);
v___x_144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_142_);
return v___x_144_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__16(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__15, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__15_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__15);
v___x_146_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__0, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__0);
v___x_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
return v___x_147_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__17(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(112u);
v___x_149_ = lean_unsigned_to_nat(8u);
v___x_150_ = l_BitVec_ofNat(v___x_149_, v___x_148_);
return v___x_150_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__18(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = lean_unsigned_to_nat(101u);
v___x_152_ = lean_unsigned_to_nat(8u);
v___x_153_ = l_BitVec_ofNat(v___x_152_, v___x_151_);
return v___x_153_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__19(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_box(0);
v___x_155_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__18, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__18_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__18);
v___x_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v___x_154_);
return v___x_156_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__20(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__19, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__19_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__19);
v___x_158_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__17, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__17_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__17);
v___x_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__21(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__20, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__20_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__20);
v___x_161_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__1, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__1);
v___x_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__22(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__21, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__21_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__21);
v___x_164_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__6, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__6);
v___x_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_163_);
return v___x_165_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__23(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_166_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__22, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__22_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__22);
v___x_167_ = lean_box(0);
v___x_168_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__16, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__16_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__16);
v___x_169_ = lean_unsigned_to_nat(404u);
v___x_170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_167_);
lean_ctor_set(v___x_170_, 3, v___x_166_);
return v___x_170_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404(void){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__23, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__23_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__23);
return v___x_171_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__0(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_unsigned_to_nat(1024u);
v___x_173_ = lean_unsigned_to_nat(64u);
v___x_174_ = l_BitVec_ofNat(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__1(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_unsigned_to_nat(1025u);
v___x_176_ = lean_unsigned_to_nat(64u);
v___x_177_ = l_BitVec_ofNat(v___x_176_, v___x_175_);
return v___x_177_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__2(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_unsigned_to_nat(1026u);
v___x_179_ = lean_unsigned_to_nat(64u);
v___x_180_ = l_BitVec_ofNat(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__3(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_unsigned_to_nat(1027u);
v___x_182_ = lean_unsigned_to_nat(64u);
v___x_183_ = l_BitVec_ofNat(v___x_182_, v___x_181_);
return v___x_183_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__4(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_unsigned_to_nat(64u);
v___x_186_ = l_BitVec_ofNat(v___x_185_, v___x_184_);
return v___x_186_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__5(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__18, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__18_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__18);
v___x_188_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_wordOfByte(v___x_187_);
return v___x_188_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__6(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__17, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__17_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__17);
v___x_190_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_wordOfByte(v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__7(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__1, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__1);
v___x_192_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_wordOfByte(v___x_191_);
return v___x_192_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__8(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__6, &lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404___closed__6);
v___x_194_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_wordOfByte(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_wmem(lean_object* v_a_195_){
_start:
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__0, &lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__0);
v___x_197_ = lean_nat_dec_eq(v_a_195_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__1, &lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__1);
v___x_199_ = lean_nat_dec_eq(v_a_195_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__2, &lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__2);
v___x_201_ = lean_nat_dec_eq(v_a_195_, v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_202_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__3, &lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__3);
v___x_203_ = lean_nat_dec_eq(v_a_195_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
v___x_204_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__4, &lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__4);
return v___x_204_;
}
else
{
lean_object* v___x_205_; 
v___x_205_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__5, &lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__5);
return v___x_205_;
}
}
else
{
lean_object* v___x_206_; 
v___x_206_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__6, &lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__6);
return v___x_206_;
}
}
else
{
lean_object* v___x_207_; 
v___x_207_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__7, &lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__7);
return v___x_207_;
}
}
else
{
lean_object* v___x_208_; 
v___x_208_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__8, &lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__8);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_wmem___boxed(lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = lp_orb_x2dcompiler_Pancake_StructEmit_wmem(v_a_209_);
lean_dec(v_a_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___lam__0(lean_object* v_x_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lean_box(0);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___lam__0___boxed(lean_object* v_x_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___lam__0(v_x_213_);
lean_dec_ref(v_x_213_);
return v_res_214_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___lam__1(lean_object* v_x_215_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = 1;
return v___x_216_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___lam__1___boxed(lean_object* v_x_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___lam__1(v_x_217_);
lean_dec(v_x_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg(lean_object* v_f_223_){
_start:
{
lean_object* v___f_224_; lean_object* v___f_225_; lean_object* v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___f_224_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___closed__0));
v___f_225_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___closed__1));
v___x_226_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg___closed__2));
v___x_227_ = 0;
v___x_228_ = lean_unsigned_to_nat(100u);
v___x_229_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__4, &lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StructEmit_wmem___closed__4);
v___x_230_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_230_, 0, v___f_224_);
lean_ctor_set(v___x_230_, 1, v___x_226_);
lean_ctor_set(v___x_230_, 2, v___f_225_);
lean_ctor_set(v___x_230_, 3, v___x_228_);
lean_ctor_set(v___x_230_, 4, v_f_223_);
lean_ctor_set(v___x_230_, 5, v___x_229_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*6, v___x_227_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_witnessState(lean_object* v_00_u03c3_231_, lean_object* v_f_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lp_orb_x2dcompiler_Pancake_StructEmit_witnessState___redArg(v_f_232_);
return v___x_233_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_SerializeStruct(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_StructEmit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_SerializeStruct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Pancake_StructEmit_resp404 = _init_lp_orb_x2dcompiler_Pancake_StructEmit_resp404();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StructEmit_resp404);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
