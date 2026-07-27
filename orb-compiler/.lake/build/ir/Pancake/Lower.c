// Lean compiler output
// Module: Pancake.Lower
// Imports: public import Init public meta import Init public import Pancake.Sem public import Dsl.EmitPancake
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
extern lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0;
lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion(lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_Lower_lowerExp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_Lower_lowerExp___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_Lower_lowerExp___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Lower_lowerExp(lean_object*);
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_Lower_lowerStmtsFold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_Lower_lowerStmtsFold___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_Lower_lowerStmtsFold___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Lower_lowerStmt1(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Lower_lowerStmtsFold(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Lower_lower(lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_Lower_regionProg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_Lower_regionProg___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_Lower_regionProg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_Lower_regionProg___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Lower_regionProg;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__8_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__8_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__6_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__6_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__7_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__7_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Lower_lowerExp(lean_object* v_x_3_){
_start:
{
switch(lean_obj_tag(v_x_3_))
{
case 0:
{
lean_object* v___x_4_; 
v___x_4_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_Lower_lowerExp___closed__0));
return v___x_4_;
}
case 1:
{
lean_object* v_n_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_15_; 
v_n_5_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_15_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_15_ == 0)
{
v___x_7_ = v_x_3_;
v_isShared_8_ = v_isSharedCheck_15_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_n_5_);
lean_dec(v_x_3_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_15_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_12_; 
v___x_9_ = lean_unsigned_to_nat(64u);
v___x_10_ = l_BitVec_ofNat(v___x_9_, v_n_5_);
lean_dec(v_n_5_);
if (v_isShared_8_ == 0)
{
lean_ctor_set_tag(v___x_7_, 0);
lean_ctor_set(v___x_7_, 0, v___x_10_);
v___x_12_ = v___x_7_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v___x_10_);
v___x_12_ = v_reuseFailAlloc_14_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
lean_object* v___x_13_; 
v___x_13_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
}
case 2:
{
lean_object* v_name_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_24_; 
v_name_16_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_24_ == 0)
{
v___x_18_ = v_x_3_;
v_isShared_19_ = v_isSharedCheck_24_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_name_16_);
lean_dec(v_x_3_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_24_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_21_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set_tag(v___x_18_, 1);
v___x_21_ = v___x_18_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_name_16_);
v___x_21_ = v_reuseFailAlloc_23_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
lean_object* v___x_22_; 
v___x_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
}
}
case 3:
{
uint8_t v_op_25_; lean_object* v_l_26_; lean_object* v_r_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_117_; 
v_op_25_ = lean_ctor_get_uint8(v_x_3_, sizeof(void*)*2);
v_l_26_ = lean_ctor_get(v_x_3_, 0);
v_r_27_ = lean_ctor_get(v_x_3_, 1);
v_isSharedCheck_117_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_117_ == 0)
{
v___x_29_ = v_x_3_;
v_isShared_30_ = v_isSharedCheck_117_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_r_27_);
lean_inc(v_l_26_);
lean_dec(v_x_3_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_117_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_31_; 
v___x_31_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_l_26_);
if (lean_obj_tag(v___x_31_) == 1)
{
lean_object* v_val_32_; lean_object* v___x_33_; 
v_val_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc(v_val_32_);
lean_dec_ref(v___x_31_);
v___x_33_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_r_27_);
if (lean_obj_tag(v___x_33_) == 1)
{
switch(v_op_25_)
{
case 0:
{
lean_object* v_val_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_45_; 
v_val_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_45_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_45_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_val_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_45_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
uint8_t v___x_38_; lean_object* v___x_40_; 
v___x_38_ = 0;
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 1, v_val_34_);
lean_ctor_set(v___x_29_, 0, v_val_32_);
v___x_40_ = v___x_29_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_val_32_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_val_34_);
v___x_40_ = v_reuseFailAlloc_44_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_42_; 
lean_ctor_set_uint8(v___x_40_, sizeof(void*)*2, v___x_38_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 0, v___x_40_);
v___x_42_ = v___x_36_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_40_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
case 1:
{
lean_object* v_val_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_54_; 
lean_del_object(v___x_29_);
v_val_46_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_54_ == 0)
{
v___x_48_ = v___x_33_;
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_val_46_);
lean_dec(v___x_33_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; lean_object* v___x_52_; 
v___x_50_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_50_, 0, v_val_32_);
lean_ctor_set(v___x_50_, 1, v_val_46_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 0, v___x_50_);
v___x_52_ = v___x_48_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_50_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
case 2:
{
lean_object* v_val_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_66_; 
v_val_55_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_66_ == 0)
{
v___x_57_ = v___x_33_;
v_isShared_58_ = v_isSharedCheck_66_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_val_55_);
lean_dec(v___x_33_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_66_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
uint8_t v___x_59_; lean_object* v___x_61_; 
v___x_59_ = 0;
if (v_isShared_30_ == 0)
{
lean_ctor_set_tag(v___x_29_, 5);
lean_ctor_set(v___x_29_, 1, v_val_55_);
lean_ctor_set(v___x_29_, 0, v_val_32_);
v___x_61_ = v___x_29_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_val_32_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v_val_55_);
v___x_61_ = v_reuseFailAlloc_65_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_63_; 
lean_ctor_set_uint8(v___x_61_, sizeof(void*)*2, v___x_59_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_61_);
v___x_63_ = v___x_57_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
case 3:
{
lean_object* v_val_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_78_; 
v_val_67_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_78_ == 0)
{
v___x_69_ = v___x_33_;
v_isShared_70_ = v_isSharedCheck_78_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_val_67_);
lean_dec(v___x_33_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_78_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
uint8_t v___x_71_; lean_object* v___x_73_; 
v___x_71_ = 1;
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 1, v_val_67_);
lean_ctor_set(v___x_29_, 0, v_val_32_);
v___x_73_ = v___x_29_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_val_32_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_val_67_);
v___x_73_ = v_reuseFailAlloc_77_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_75_; 
lean_ctor_set_uint8(v___x_73_, sizeof(void*)*2, v___x_71_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_73_);
v___x_75_ = v___x_69_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_73_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
}
case 4:
{
lean_object* v_val_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_90_; 
v_val_79_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_90_ == 0)
{
v___x_81_ = v___x_33_;
v_isShared_82_ = v_isSharedCheck_90_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_val_79_);
lean_dec(v___x_33_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_90_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
uint8_t v___x_83_; lean_object* v___x_85_; 
v___x_83_ = 1;
if (v_isShared_30_ == 0)
{
lean_ctor_set_tag(v___x_29_, 5);
lean_ctor_set(v___x_29_, 1, v_val_79_);
lean_ctor_set(v___x_29_, 0, v_val_32_);
v___x_85_ = v___x_29_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_val_32_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_val_79_);
v___x_85_ = v_reuseFailAlloc_89_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_87_; 
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*2, v___x_83_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v___x_85_);
v___x_87_ = v___x_81_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
case 5:
{
lean_object* v_val_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_102_; 
v_val_91_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_102_ == 0)
{
v___x_93_ = v___x_33_;
v_isShared_94_ = v_isSharedCheck_102_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_val_91_);
lean_dec(v___x_33_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_102_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
uint8_t v___x_95_; lean_object* v___x_97_; 
v___x_95_ = 2;
if (v_isShared_30_ == 0)
{
lean_ctor_set_tag(v___x_29_, 5);
lean_ctor_set(v___x_29_, 1, v_val_32_);
lean_ctor_set(v___x_29_, 0, v_val_91_);
v___x_97_ = v___x_29_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_val_91_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_val_32_);
v___x_97_ = v_reuseFailAlloc_101_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_99_; 
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*2, v___x_95_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_97_);
v___x_99_ = v___x_93_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
default: 
{
lean_object* v_val_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_114_; 
v_val_103_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_114_ == 0)
{
v___x_105_ = v___x_33_;
v_isShared_106_ = v_isSharedCheck_114_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_val_103_);
lean_dec(v___x_33_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_114_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
uint8_t v___x_107_; lean_object* v___x_109_; 
v___x_107_ = 2;
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 1, v_val_103_);
lean_ctor_set(v___x_29_, 0, v_val_32_);
v___x_109_ = v___x_29_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_val_32_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_val_103_);
v___x_109_ = v_reuseFailAlloc_113_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_111_; 
lean_ctor_set_uint8(v___x_109_, sizeof(void*)*2, v___x_107_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_109_);
v___x_111_ = v___x_105_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
}
else
{
lean_object* v___x_115_; 
lean_dec(v___x_33_);
lean_dec(v_val_32_);
lean_del_object(v___x_29_);
v___x_115_ = lean_box(0);
return v___x_115_;
}
}
else
{
lean_object* v___x_116_; 
lean_dec(v___x_31_);
lean_del_object(v___x_29_);
lean_dec(v_r_27_);
v___x_116_ = lean_box(0);
return v___x_116_;
}
}
}
case 4:
{
lean_object* v_addr_118_; lean_object* v___x_119_; 
v_addr_118_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_addr_118_);
lean_dec_ref(v_x_3_);
v___x_119_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_addr_118_);
if (lean_obj_tag(v___x_119_) == 0)
{
return v___x_119_;
}
else
{
lean_object* v_val_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_128_; 
v_val_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_128_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_128_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_val_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_128_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_124_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_124_, 0, v_val_120_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v___x_124_);
v___x_126_ = v___x_122_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
default: 
{
lean_object* v_addr_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_145_; 
v_addr_129_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_145_ == 0)
{
v___x_131_ = v_x_3_;
v_isShared_132_ = v_isSharedCheck_145_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_addr_129_);
lean_dec(v_x_3_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_145_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; 
v___x_133_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_addr_129_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_del_object(v___x_131_);
return v___x_133_;
}
else
{
lean_object* v_val_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_144_; 
v_val_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_144_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_144_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_val_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_144_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set_tag(v___x_131_, 6);
lean_ctor_set(v___x_131_, 0, v_val_134_);
v___x_139_ = v___x_131_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_val_134_);
v___x_139_ = v_reuseFailAlloc_143_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_141_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_139_);
v___x_141_ = v___x_136_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Lower_lowerStmt1(lean_object* v_x_148_){
_start:
{
switch(lean_obj_tag(v_x_148_))
{
case 0:
{
lean_object* v_name_149_; lean_object* v_val_150_; lean_object* v___x_151_; 
v_name_149_ = lean_ctor_get(v_x_148_, 0);
lean_inc_ref(v_name_149_);
v_val_150_ = lean_ctor_get(v_x_148_, 1);
lean_inc(v_val_150_);
lean_dec_ref(v_x_148_);
v___x_151_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_val_150_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v___x_152_; 
lean_dec_ref(v_name_149_);
v___x_152_ = lean_box(0);
return v___x_152_;
}
else
{
lean_object* v_val_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_162_; 
v_val_153_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_162_ == 0)
{
v___x_155_ = v___x_151_;
v_isShared_156_ = v_isSharedCheck_162_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_val_153_);
lean_dec(v___x_151_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_162_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_157_ = lean_box(0);
v___x_158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_158_, 0, v_name_149_);
lean_ctor_set(v___x_158_, 1, v_val_153_);
lean_ctor_set(v___x_158_, 2, v___x_157_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_158_);
v___x_160_ = v___x_155_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
case 1:
{
lean_object* v_name_163_; lean_object* v_val_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_181_; 
v_name_163_ = lean_ctor_get(v_x_148_, 0);
v_val_164_ = lean_ctor_get(v_x_148_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_x_148_);
if (v_isSharedCheck_181_ == 0)
{
v___x_166_ = v_x_148_;
v_isShared_167_ = v_isSharedCheck_181_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_val_164_);
lean_inc(v_name_163_);
lean_dec(v_x_148_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_181_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; 
v___x_168_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_val_164_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v___x_169_; 
lean_del_object(v___x_166_);
lean_dec_ref(v_name_163_);
v___x_169_ = lean_box(0);
return v___x_169_;
}
else
{
lean_object* v_val_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_180_; 
v_val_170_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_180_ == 0)
{
v___x_172_ = v___x_168_;
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_val_170_);
lean_dec(v___x_168_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set_tag(v___x_166_, 2);
lean_ctor_set(v___x_166_, 1, v_val_170_);
v___x_175_ = v___x_166_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_name_163_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_val_170_);
v___x_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_177_; 
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_175_);
v___x_177_ = v___x_172_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
}
case 2:
{
lean_object* v_addr_182_; lean_object* v_val_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_203_; 
v_addr_182_ = lean_ctor_get(v_x_148_, 0);
v_val_183_ = lean_ctor_get(v_x_148_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_x_148_);
if (v_isSharedCheck_203_ == 0)
{
v___x_185_ = v_x_148_;
v_isShared_186_ = v_isSharedCheck_203_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_val_183_);
lean_inc(v_addr_182_);
lean_dec(v_x_148_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_203_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; 
v___x_187_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_addr_182_);
if (lean_obj_tag(v___x_187_) == 1)
{
lean_object* v_val_188_; lean_object* v___x_189_; 
v_val_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_val_188_);
lean_dec_ref(v___x_187_);
v___x_189_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_val_183_);
if (lean_obj_tag(v___x_189_) == 1)
{
lean_object* v_val_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_200_; 
v_val_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_200_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_val_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set_tag(v___x_185_, 3);
lean_ctor_set(v___x_185_, 1, v_val_190_);
lean_ctor_set(v___x_185_, 0, v_val_188_);
v___x_195_ = v___x_185_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_val_188_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_val_190_);
v___x_195_ = v_reuseFailAlloc_199_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_195_);
v___x_197_ = v___x_192_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_object* v___x_201_; 
lean_dec(v___x_189_);
lean_dec(v_val_188_);
lean_del_object(v___x_185_);
v___x_201_ = lean_box(0);
return v___x_201_;
}
}
else
{
lean_object* v___x_202_; 
lean_dec(v___x_187_);
lean_del_object(v___x_185_);
lean_dec(v_val_183_);
v___x_202_ = lean_box(0);
return v___x_202_;
}
}
}
case 3:
{
lean_object* v_addr_204_; lean_object* v_val_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_225_; 
v_addr_204_ = lean_ctor_get(v_x_148_, 0);
v_val_205_ = lean_ctor_get(v_x_148_, 1);
v_isSharedCheck_225_ = !lean_is_exclusive(v_x_148_);
if (v_isSharedCheck_225_ == 0)
{
v___x_207_ = v_x_148_;
v_isShared_208_ = v_isSharedCheck_225_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_val_205_);
lean_inc(v_addr_204_);
lean_dec(v_x_148_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_225_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; 
v___x_209_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_addr_204_);
if (lean_obj_tag(v___x_209_) == 1)
{
lean_object* v_val_210_; lean_object* v___x_211_; 
v_val_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_val_210_);
lean_dec_ref(v___x_209_);
v___x_211_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_val_205_);
if (lean_obj_tag(v___x_211_) == 1)
{
lean_object* v_val_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_222_; 
v_val_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_222_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_222_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_val_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_222_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_208_ == 0)
{
lean_ctor_set_tag(v___x_207_, 9);
lean_ctor_set(v___x_207_, 1, v_val_212_);
lean_ctor_set(v___x_207_, 0, v_val_210_);
v___x_217_ = v___x_207_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_val_210_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_val_212_);
v___x_217_ = v_reuseFailAlloc_221_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_219_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_217_);
v___x_219_ = v___x_214_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
else
{
lean_object* v___x_223_; 
lean_dec(v___x_211_);
lean_dec(v_val_210_);
lean_del_object(v___x_207_);
v___x_223_ = lean_box(0);
return v___x_223_;
}
}
else
{
lean_object* v___x_224_; 
lean_dec(v___x_209_);
lean_del_object(v___x_207_);
lean_dec(v_val_205_);
v___x_224_ = lean_box(0);
return v___x_224_;
}
}
}
case 4:
{
lean_object* v_name_226_; lean_object* v_args_227_; 
v_name_226_ = lean_ctor_get(v_x_148_, 0);
lean_inc_ref(v_name_226_);
v_args_227_ = lean_ctor_get(v_x_148_, 1);
lean_inc(v_args_227_);
lean_dec_ref(v_x_148_);
if (lean_obj_tag(v_args_227_) == 1)
{
lean_object* v_tail_232_; 
v_tail_232_ = lean_ctor_get(v_args_227_, 1);
lean_inc(v_tail_232_);
if (lean_obj_tag(v_tail_232_) == 1)
{
lean_object* v_tail_233_; 
v_tail_233_ = lean_ctor_get(v_tail_232_, 1);
lean_inc(v_tail_233_);
if (lean_obj_tag(v_tail_233_) == 1)
{
lean_object* v_tail_234_; 
v_tail_234_ = lean_ctor_get(v_tail_233_, 1);
lean_inc(v_tail_234_);
if (lean_obj_tag(v_tail_234_) == 1)
{
lean_object* v_head_235_; lean_object* v_head_236_; lean_object* v_head_237_; lean_object* v_head_238_; lean_object* v___x_239_; 
v_head_235_ = lean_ctor_get(v_args_227_, 0);
lean_inc(v_head_235_);
lean_dec_ref(v_args_227_);
v_head_236_ = lean_ctor_get(v_tail_232_, 0);
lean_inc(v_head_236_);
lean_dec_ref(v_tail_232_);
v_head_237_ = lean_ctor_get(v_tail_233_, 0);
lean_inc(v_head_237_);
lean_dec_ref(v_tail_233_);
v_head_238_ = lean_ctor_get(v_tail_234_, 0);
lean_inc(v_head_238_);
lean_dec_ref(v_tail_234_);
v___x_239_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_head_235_);
if (lean_obj_tag(v___x_239_) == 1)
{
lean_object* v_val_240_; lean_object* v___x_241_; 
v_val_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_val_240_);
lean_dec_ref(v___x_239_);
v___x_241_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_head_236_);
if (lean_obj_tag(v___x_241_) == 1)
{
lean_object* v_val_242_; lean_object* v___x_243_; 
v_val_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_val_242_);
lean_dec_ref(v___x_241_);
v___x_243_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_head_237_);
if (lean_obj_tag(v___x_243_) == 1)
{
lean_object* v_val_244_; lean_object* v___x_245_; 
v_val_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_val_244_);
lean_dec_ref(v___x_243_);
v___x_245_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_head_238_);
if (lean_obj_tag(v___x_245_) == 1)
{
lean_object* v_val_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_254_; 
v_val_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_254_ == 0)
{
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_val_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_250_ = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(v___x_250_, 0, v_name_226_);
lean_ctor_set(v___x_250_, 1, v_val_240_);
lean_ctor_set(v___x_250_, 2, v_val_242_);
lean_ctor_set(v___x_250_, 3, v_val_244_);
lean_ctor_set(v___x_250_, 4, v_val_246_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_250_);
v___x_252_ = v___x_248_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
else
{
lean_object* v___x_255_; 
lean_dec(v___x_245_);
lean_dec(v_val_244_);
lean_dec(v_val_242_);
lean_dec(v_val_240_);
lean_dec_ref(v_name_226_);
v___x_255_ = lean_box(0);
return v___x_255_;
}
}
else
{
lean_object* v___x_256_; 
lean_dec(v___x_243_);
lean_dec(v_val_242_);
lean_dec(v_val_240_);
lean_dec(v_head_238_);
lean_dec_ref(v_name_226_);
v___x_256_ = lean_box(0);
return v___x_256_;
}
}
else
{
lean_object* v___x_257_; 
lean_dec(v___x_241_);
lean_dec(v_val_240_);
lean_dec(v_head_238_);
lean_dec(v_head_237_);
lean_dec_ref(v_name_226_);
v___x_257_ = lean_box(0);
return v___x_257_;
}
}
else
{
lean_object* v___x_258_; 
lean_dec(v___x_239_);
lean_dec(v_head_238_);
lean_dec(v_head_237_);
lean_dec(v_head_236_);
lean_dec_ref(v_name_226_);
v___x_258_ = lean_box(0);
return v___x_258_;
}
}
else
{
lean_dec_ref(v_tail_233_);
lean_dec(v_tail_234_);
lean_dec_ref(v_tail_232_);
lean_dec_ref(v_args_227_);
goto v___jp_228_;
}
}
else
{
lean_dec_ref(v_tail_232_);
lean_dec(v_tail_233_);
lean_dec_ref(v_args_227_);
goto v___jp_228_;
}
}
else
{
lean_dec(v_tail_232_);
lean_dec_ref(v_args_227_);
goto v___jp_228_;
}
}
else
{
lean_dec(v_args_227_);
goto v___jp_228_;
}
v___jp_228_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_box(2);
v___x_230_ = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(v___x_230_, 0, v_name_226_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
lean_ctor_set(v___x_230_, 2, v___x_229_);
lean_ctor_set(v___x_230_, 3, v___x_229_);
lean_ctor_set(v___x_230_, 4, v___x_229_);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
case 5:
{
lean_object* v___x_259_; 
lean_dec_ref(v_x_148_);
v___x_259_ = lean_box(0);
return v___x_259_;
}
case 6:
{
lean_object* v_val_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_277_; 
v_val_260_ = lean_ctor_get(v_x_148_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_148_);
if (v_isSharedCheck_277_ == 0)
{
v___x_262_ = v_x_148_;
v_isShared_263_ = v_isSharedCheck_277_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_val_260_);
lean_dec(v_x_148_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_277_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; 
v___x_264_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_val_260_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_265_; 
lean_del_object(v___x_262_);
v___x_265_ = lean_box(0);
return v___x_265_;
}
else
{
lean_object* v_val_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_276_; 
v_val_266_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_276_ == 0)
{
v___x_268_ = v___x_264_;
v_isShared_269_ = v_isSharedCheck_276_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_val_266_);
lean_dec(v___x_264_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_276_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set_tag(v___x_262_, 8);
lean_ctor_set(v___x_262_, 0, v_val_266_);
v___x_271_ = v___x_262_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_val_266_);
v___x_271_ = v_reuseFailAlloc_275_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_273_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_271_);
v___x_273_ = v___x_268_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
}
case 7:
{
lean_object* v_cond_278_; lean_object* v_thn_279_; lean_object* v_els_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_303_; 
v_cond_278_ = lean_ctor_get(v_x_148_, 0);
v_thn_279_ = lean_ctor_get(v_x_148_, 1);
v_els_280_ = lean_ctor_get(v_x_148_, 2);
v_isSharedCheck_303_ = !lean_is_exclusive(v_x_148_);
if (v_isSharedCheck_303_ == 0)
{
v___x_282_ = v_x_148_;
v_isShared_283_ = v_isSharedCheck_303_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_els_280_);
lean_inc(v_thn_279_);
lean_inc(v_cond_278_);
lean_dec(v_x_148_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_303_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; 
v___x_284_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_cond_278_);
if (lean_obj_tag(v___x_284_) == 1)
{
lean_object* v_val_285_; lean_object* v___x_286_; 
v_val_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_val_285_);
lean_dec_ref(v___x_284_);
v___x_286_ = lp_orb_x2dcompiler_Pancake_Lower_lowerStmtsFold(v_thn_279_);
if (lean_obj_tag(v___x_286_) == 1)
{
lean_object* v_val_287_; lean_object* v___x_288_; 
v_val_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_val_287_);
lean_dec_ref(v___x_286_);
v___x_288_ = lp_orb_x2dcompiler_Pancake_Lower_lowerStmtsFold(v_els_280_);
if (lean_obj_tag(v___x_288_) == 1)
{
lean_object* v_val_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_299_; 
v_val_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_299_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_299_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_val_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_299_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set_tag(v___x_282_, 6);
lean_ctor_set(v___x_282_, 2, v_val_289_);
lean_ctor_set(v___x_282_, 1, v_val_287_);
lean_ctor_set(v___x_282_, 0, v_val_285_);
v___x_294_ = v___x_282_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_val_285_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_val_287_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_val_289_);
v___x_294_ = v_reuseFailAlloc_298_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_296_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_294_);
v___x_296_ = v___x_291_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
lean_object* v___x_300_; 
lean_dec(v___x_288_);
lean_dec(v_val_287_);
lean_dec(v_val_285_);
lean_del_object(v___x_282_);
v___x_300_ = lean_box(0);
return v___x_300_;
}
}
else
{
lean_object* v___x_301_; 
lean_dec(v___x_286_);
lean_dec(v_val_285_);
lean_del_object(v___x_282_);
lean_dec(v_els_280_);
v___x_301_ = lean_box(0);
return v___x_301_;
}
}
else
{
lean_object* v___x_302_; 
lean_dec(v___x_284_);
lean_del_object(v___x_282_);
lean_dec(v_els_280_);
lean_dec(v_thn_279_);
v___x_302_ = lean_box(0);
return v___x_302_;
}
}
}
default: 
{
lean_object* v_cond_304_; lean_object* v_body_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_325_; 
v_cond_304_ = lean_ctor_get(v_x_148_, 0);
v_body_305_ = lean_ctor_get(v_x_148_, 1);
v_isSharedCheck_325_ = !lean_is_exclusive(v_x_148_);
if (v_isSharedCheck_325_ == 0)
{
v___x_307_ = v_x_148_;
v_isShared_308_ = v_isSharedCheck_325_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_body_305_);
lean_inc(v_cond_304_);
lean_dec(v_x_148_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_325_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; 
v___x_309_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_cond_304_);
if (lean_obj_tag(v___x_309_) == 1)
{
lean_object* v_val_310_; lean_object* v___x_311_; 
v_val_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_val_310_);
lean_dec_ref(v___x_309_);
v___x_311_ = lp_orb_x2dcompiler_Pancake_Lower_lowerStmtsFold(v_body_305_);
if (lean_obj_tag(v___x_311_) == 1)
{
lean_object* v_val_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_322_; 
v_val_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_322_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_322_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_val_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_322_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 7);
lean_ctor_set(v___x_307_, 1, v_val_312_);
lean_ctor_set(v___x_307_, 0, v_val_310_);
v___x_317_ = v___x_307_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_val_310_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_val_312_);
v___x_317_ = v_reuseFailAlloc_321_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_319_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_317_);
v___x_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
else
{
lean_object* v___x_323_; 
lean_dec(v___x_311_);
lean_dec(v_val_310_);
lean_del_object(v___x_307_);
v___x_323_ = lean_box(0);
return v___x_323_;
}
}
else
{
lean_object* v___x_324_; 
lean_dec(v___x_309_);
lean_del_object(v___x_307_);
lean_dec(v_body_305_);
v___x_324_ = lean_box(0);
return v___x_324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Lower_lowerStmtsFold(lean_object* v_x_326_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
lean_object* v___x_327_; 
v___x_327_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_Lower_lowerStmtsFold___closed__0));
return v___x_327_;
}
else
{
lean_object* v_tail_328_; 
v_tail_328_ = lean_ctor_get(v_x_326_, 1);
if (lean_obj_tag(v_tail_328_) == 0)
{
lean_object* v_head_329_; lean_object* v___x_330_; 
v_head_329_ = lean_ctor_get(v_x_326_, 0);
lean_inc(v_head_329_);
lean_dec_ref(v_x_326_);
v___x_330_ = lp_orb_x2dcompiler_Pancake_Lower_lowerStmt1(v_head_329_);
return v___x_330_;
}
else
{
lean_object* v_head_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_367_; 
lean_inc(v_tail_328_);
v_head_331_ = lean_ctor_get(v_x_326_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v_x_326_);
if (v_isSharedCheck_367_ == 0)
{
lean_object* v_unused_368_; 
v_unused_368_ = lean_ctor_get(v_x_326_, 1);
lean_dec(v_unused_368_);
v___x_333_ = v_x_326_;
v_isShared_334_ = v_isSharedCheck_367_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_head_331_);
lean_dec(v_x_326_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_367_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
if (lean_obj_tag(v_head_331_) == 0)
{
lean_object* v_name_335_; lean_object* v_val_336_; lean_object* v___x_337_; 
lean_del_object(v___x_333_);
v_name_335_ = lean_ctor_get(v_head_331_, 0);
lean_inc_ref(v_name_335_);
v_val_336_ = lean_ctor_get(v_head_331_, 1);
lean_inc(v_val_336_);
lean_dec_ref(v_head_331_);
v___x_337_ = lp_orb_x2dcompiler_Pancake_Lower_lowerExp(v_val_336_);
if (lean_obj_tag(v___x_337_) == 1)
{
lean_object* v_val_338_; lean_object* v___x_339_; 
v_val_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_val_338_);
lean_dec_ref(v___x_337_);
v___x_339_ = lp_orb_x2dcompiler_Pancake_Lower_lowerStmtsFold(v_tail_328_);
if (lean_obj_tag(v___x_339_) == 1)
{
lean_object* v_val_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_348_; 
v_val_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_348_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_val_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_344_, 0, v_name_335_);
lean_ctor_set(v___x_344_, 1, v_val_338_);
lean_ctor_set(v___x_344_, 2, v_val_340_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_344_);
v___x_346_ = v___x_342_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_object* v___x_349_; 
lean_dec(v___x_339_);
lean_dec(v_val_338_);
lean_dec_ref(v_name_335_);
v___x_349_ = lean_box(0);
return v___x_349_;
}
}
else
{
lean_object* v___x_350_; 
lean_dec(v___x_337_);
lean_dec_ref(v_name_335_);
lean_dec(v_tail_328_);
v___x_350_ = lean_box(0);
return v___x_350_;
}
}
else
{
lean_object* v___x_351_; 
v___x_351_ = lp_orb_x2dcompiler_Pancake_Lower_lowerStmt1(v_head_331_);
if (lean_obj_tag(v___x_351_) == 1)
{
lean_object* v_val_352_; lean_object* v___x_353_; 
v_val_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_val_352_);
lean_dec_ref(v___x_351_);
v___x_353_ = lp_orb_x2dcompiler_Pancake_Lower_lowerStmtsFold(v_tail_328_);
if (lean_obj_tag(v___x_353_) == 1)
{
lean_object* v_val_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_364_; 
v_val_354_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_364_ == 0)
{
v___x_356_ = v___x_353_;
v_isShared_357_ = v_isSharedCheck_364_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_val_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_364_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set_tag(v___x_333_, 5);
lean_ctor_set(v___x_333_, 1, v_val_354_);
lean_ctor_set(v___x_333_, 0, v_val_352_);
v___x_359_ = v___x_333_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_val_352_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_val_354_);
v___x_359_ = v_reuseFailAlloc_363_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_361_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_359_);
v___x_361_ = v___x_356_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v___x_365_; 
lean_dec(v___x_353_);
lean_dec(v_val_352_);
lean_del_object(v___x_333_);
v___x_365_ = lean_box(0);
return v___x_365_;
}
}
else
{
lean_object* v___x_366_; 
lean_dec(v___x_351_);
lean_del_object(v___x_333_);
lean_dec(v_tail_328_);
v___x_366_ = lean_box(0);
return v___x_366_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Lower_lower(lean_object* v_f_369_){
_start:
{
lean_object* v_body_370_; lean_object* v___x_371_; 
v_body_370_ = lean_ctor_get(v_f_369_, 2);
lean_inc(v_body_370_);
lean_dec_ref(v_f_369_);
v___x_371_ = lp_orb_x2dcompiler_Pancake_Lower_lowerStmtsFold(v_body_370_);
return v___x_371_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_Lower_regionProg___closed__0(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0;
v___x_373_ = lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_Lower_regionProg___closed__1(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_Lower_regionProg___closed__0, &lp_orb_x2dcompiler_Pancake_Lower_regionProg___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_Lower_regionProg___closed__0);
v___x_375_ = lp_orb_x2dcompiler_Pancake_Lower_lower(v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_Lower_regionProg(void){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_Lower_regionProg___closed__1, &lp_orb_x2dcompiler_Pancake_Lower_regionProg___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_Lower_regionProg___closed__1);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__8_splitter___redArg(lean_object* v_x_377_, lean_object* v_h__1_378_, lean_object* v_h__2_379_, lean_object* v_h__3_380_, lean_object* v_h__4_381_, lean_object* v_h__5_382_, lean_object* v_h__6_383_){
_start:
{
switch(lean_obj_tag(v_x_377_))
{
case 0:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec(v_h__6_383_);
lean_dec(v_h__5_382_);
lean_dec(v_h__4_381_);
lean_dec(v_h__3_380_);
lean_dec(v_h__2_379_);
v___x_384_ = lean_box(0);
v___x_385_ = lean_apply_1(v_h__1_378_, v___x_384_);
return v___x_385_;
}
case 1:
{
lean_object* v_n_386_; lean_object* v___x_387_; 
lean_dec(v_h__6_383_);
lean_dec(v_h__5_382_);
lean_dec(v_h__4_381_);
lean_dec(v_h__3_380_);
lean_dec(v_h__1_378_);
v_n_386_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_n_386_);
lean_dec_ref(v_x_377_);
v___x_387_ = lean_apply_1(v_h__2_379_, v_n_386_);
return v___x_387_;
}
case 2:
{
lean_object* v_name_388_; lean_object* v___x_389_; 
lean_dec(v_h__6_383_);
lean_dec(v_h__5_382_);
lean_dec(v_h__4_381_);
lean_dec(v_h__2_379_);
lean_dec(v_h__1_378_);
v_name_388_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_name_388_);
lean_dec_ref(v_x_377_);
v___x_389_ = lean_apply_1(v_h__3_380_, v_name_388_);
return v___x_389_;
}
case 3:
{
uint8_t v_op_390_; lean_object* v_l_391_; lean_object* v_r_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v_h__6_383_);
lean_dec(v_h__5_382_);
lean_dec(v_h__3_380_);
lean_dec(v_h__2_379_);
lean_dec(v_h__1_378_);
v_op_390_ = lean_ctor_get_uint8(v_x_377_, sizeof(void*)*2);
v_l_391_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_l_391_);
v_r_392_ = lean_ctor_get(v_x_377_, 1);
lean_inc(v_r_392_);
lean_dec_ref(v_x_377_);
v___x_393_ = lean_box(v_op_390_);
v___x_394_ = lean_apply_3(v_h__4_381_, v___x_393_, v_l_391_, v_r_392_);
return v___x_394_;
}
case 4:
{
lean_object* v_shape_395_; lean_object* v_addr_396_; lean_object* v___x_397_; 
lean_dec(v_h__6_383_);
lean_dec(v_h__4_381_);
lean_dec(v_h__3_380_);
lean_dec(v_h__2_379_);
lean_dec(v_h__1_378_);
v_shape_395_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_shape_395_);
v_addr_396_ = lean_ctor_get(v_x_377_, 1);
lean_inc(v_addr_396_);
lean_dec_ref(v_x_377_);
v___x_397_ = lean_apply_2(v_h__5_382_, v_shape_395_, v_addr_396_);
return v___x_397_;
}
default: 
{
lean_object* v_addr_398_; lean_object* v___x_399_; 
lean_dec(v_h__5_382_);
lean_dec(v_h__4_381_);
lean_dec(v_h__3_380_);
lean_dec(v_h__2_379_);
lean_dec(v_h__1_378_);
v_addr_398_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_addr_398_);
lean_dec_ref(v_x_377_);
v___x_399_ = lean_apply_1(v_h__6_383_, v_addr_398_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__8_splitter(lean_object* v_motive_400_, lean_object* v_x_401_, lean_object* v_h__1_402_, lean_object* v_h__2_403_, lean_object* v_h__3_404_, lean_object* v_h__4_405_, lean_object* v_h__5_406_, lean_object* v_h__6_407_){
_start:
{
switch(lean_obj_tag(v_x_401_))
{
case 0:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec(v_h__6_407_);
lean_dec(v_h__5_406_);
lean_dec(v_h__4_405_);
lean_dec(v_h__3_404_);
lean_dec(v_h__2_403_);
v___x_408_ = lean_box(0);
v___x_409_ = lean_apply_1(v_h__1_402_, v___x_408_);
return v___x_409_;
}
case 1:
{
lean_object* v_n_410_; lean_object* v___x_411_; 
lean_dec(v_h__6_407_);
lean_dec(v_h__5_406_);
lean_dec(v_h__4_405_);
lean_dec(v_h__3_404_);
lean_dec(v_h__1_402_);
v_n_410_ = lean_ctor_get(v_x_401_, 0);
lean_inc(v_n_410_);
lean_dec_ref(v_x_401_);
v___x_411_ = lean_apply_1(v_h__2_403_, v_n_410_);
return v___x_411_;
}
case 2:
{
lean_object* v_name_412_; lean_object* v___x_413_; 
lean_dec(v_h__6_407_);
lean_dec(v_h__5_406_);
lean_dec(v_h__4_405_);
lean_dec(v_h__2_403_);
lean_dec(v_h__1_402_);
v_name_412_ = lean_ctor_get(v_x_401_, 0);
lean_inc_ref(v_name_412_);
lean_dec_ref(v_x_401_);
v___x_413_ = lean_apply_1(v_h__3_404_, v_name_412_);
return v___x_413_;
}
case 3:
{
uint8_t v_op_414_; lean_object* v_l_415_; lean_object* v_r_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec(v_h__6_407_);
lean_dec(v_h__5_406_);
lean_dec(v_h__3_404_);
lean_dec(v_h__2_403_);
lean_dec(v_h__1_402_);
v_op_414_ = lean_ctor_get_uint8(v_x_401_, sizeof(void*)*2);
v_l_415_ = lean_ctor_get(v_x_401_, 0);
lean_inc(v_l_415_);
v_r_416_ = lean_ctor_get(v_x_401_, 1);
lean_inc(v_r_416_);
lean_dec_ref(v_x_401_);
v___x_417_ = lean_box(v_op_414_);
v___x_418_ = lean_apply_3(v_h__4_405_, v___x_417_, v_l_415_, v_r_416_);
return v___x_418_;
}
case 4:
{
lean_object* v_shape_419_; lean_object* v_addr_420_; lean_object* v___x_421_; 
lean_dec(v_h__6_407_);
lean_dec(v_h__4_405_);
lean_dec(v_h__3_404_);
lean_dec(v_h__2_403_);
lean_dec(v_h__1_402_);
v_shape_419_ = lean_ctor_get(v_x_401_, 0);
lean_inc(v_shape_419_);
v_addr_420_ = lean_ctor_get(v_x_401_, 1);
lean_inc(v_addr_420_);
lean_dec_ref(v_x_401_);
v___x_421_ = lean_apply_2(v_h__5_406_, v_shape_419_, v_addr_420_);
return v___x_421_;
}
default: 
{
lean_object* v_addr_422_; lean_object* v___x_423_; 
lean_dec(v_h__5_406_);
lean_dec(v_h__4_405_);
lean_dec(v_h__3_404_);
lean_dec(v_h__2_403_);
lean_dec(v_h__1_402_);
v_addr_422_ = lean_ctor_get(v_x_401_, 0);
lean_inc(v_addr_422_);
lean_dec_ref(v_x_401_);
v___x_423_ = lean_apply_1(v_h__6_407_, v_addr_422_);
return v___x_423_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__3_splitter___redArg(lean_object* v_x_424_, lean_object* v_x_425_, lean_object* v_h__1_426_, lean_object* v_h__2_427_){
_start:
{
if (lean_obj_tag(v_x_424_) == 1)
{
if (lean_obj_tag(v_x_425_) == 1)
{
lean_object* v_val_428_; lean_object* v_val_429_; lean_object* v___x_430_; 
lean_dec(v_h__2_427_);
v_val_428_ = lean_ctor_get(v_x_424_, 0);
lean_inc(v_val_428_);
lean_dec_ref(v_x_424_);
v_val_429_ = lean_ctor_get(v_x_425_, 0);
lean_inc(v_val_429_);
lean_dec_ref(v_x_425_);
v___x_430_ = lean_apply_2(v_h__1_426_, v_val_428_, v_val_429_);
return v___x_430_;
}
else
{
lean_object* v___x_431_; 
lean_dec(v_h__1_426_);
v___x_431_ = lean_apply_3(v_h__2_427_, v_x_424_, v_x_425_, lean_box(0));
return v___x_431_;
}
}
else
{
lean_object* v___x_432_; 
lean_dec(v_h__1_426_);
v___x_432_ = lean_apply_3(v_h__2_427_, v_x_424_, v_x_425_, lean_box(0));
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__3_splitter(lean_object* v_motive_433_, lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_h__1_436_, lean_object* v_h__2_437_){
_start:
{
if (lean_obj_tag(v_x_434_) == 1)
{
if (lean_obj_tag(v_x_435_) == 1)
{
lean_object* v_val_438_; lean_object* v_val_439_; lean_object* v___x_440_; 
lean_dec(v_h__2_437_);
v_val_438_ = lean_ctor_get(v_x_434_, 0);
lean_inc(v_val_438_);
lean_dec_ref(v_x_434_);
v_val_439_ = lean_ctor_get(v_x_435_, 0);
lean_inc(v_val_439_);
lean_dec_ref(v_x_435_);
v___x_440_ = lean_apply_2(v_h__1_436_, v_val_438_, v_val_439_);
return v___x_440_;
}
else
{
lean_object* v___x_441_; 
lean_dec(v_h__1_436_);
v___x_441_ = lean_apply_3(v_h__2_437_, v_x_434_, v_x_435_, lean_box(0));
return v___x_441_;
}
}
else
{
lean_object* v___x_442_; 
lean_dec(v_h__1_436_);
v___x_442_ = lean_apply_3(v_h__2_437_, v_x_434_, v_x_435_, lean_box(0));
return v___x_442_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__1_splitter___redArg(uint8_t v_op_443_, lean_object* v_h__1_444_, lean_object* v_h__2_445_, lean_object* v_h__3_446_, lean_object* v_h__4_447_, lean_object* v_h__5_448_, lean_object* v_h__6_449_, lean_object* v_h__7_450_){
_start:
{
switch(v_op_443_)
{
case 0:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec(v_h__7_450_);
lean_dec(v_h__6_449_);
lean_dec(v_h__5_448_);
lean_dec(v_h__4_447_);
lean_dec(v_h__3_446_);
lean_dec(v_h__2_445_);
v___x_451_ = lean_box(0);
v___x_452_ = lean_apply_1(v_h__1_444_, v___x_451_);
return v___x_452_;
}
case 1:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec(v_h__7_450_);
lean_dec(v_h__6_449_);
lean_dec(v_h__5_448_);
lean_dec(v_h__4_447_);
lean_dec(v_h__2_445_);
lean_dec(v_h__1_444_);
v___x_453_ = lean_box(0);
v___x_454_ = lean_apply_1(v_h__3_446_, v___x_453_);
return v___x_454_;
}
case 2:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec(v_h__7_450_);
lean_dec(v_h__6_449_);
lean_dec(v_h__5_448_);
lean_dec(v_h__3_446_);
lean_dec(v_h__2_445_);
lean_dec(v_h__1_444_);
v___x_455_ = lean_box(0);
v___x_456_ = lean_apply_1(v_h__4_447_, v___x_455_);
return v___x_456_;
}
case 3:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec(v_h__7_450_);
lean_dec(v_h__6_449_);
lean_dec(v_h__5_448_);
lean_dec(v_h__4_447_);
lean_dec(v_h__3_446_);
lean_dec(v_h__1_444_);
v___x_457_ = lean_box(0);
v___x_458_ = lean_apply_1(v_h__2_445_, v___x_457_);
return v___x_458_;
}
case 4:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec(v_h__7_450_);
lean_dec(v_h__6_449_);
lean_dec(v_h__4_447_);
lean_dec(v_h__3_446_);
lean_dec(v_h__2_445_);
lean_dec(v_h__1_444_);
v___x_459_ = lean_box(0);
v___x_460_ = lean_apply_1(v_h__5_448_, v___x_459_);
return v___x_460_;
}
case 5:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
lean_dec(v_h__7_450_);
lean_dec(v_h__5_448_);
lean_dec(v_h__4_447_);
lean_dec(v_h__3_446_);
lean_dec(v_h__2_445_);
lean_dec(v_h__1_444_);
v___x_461_ = lean_box(0);
v___x_462_ = lean_apply_1(v_h__6_449_, v___x_461_);
return v___x_462_;
}
default: 
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec(v_h__6_449_);
lean_dec(v_h__5_448_);
lean_dec(v_h__4_447_);
lean_dec(v_h__3_446_);
lean_dec(v_h__2_445_);
lean_dec(v_h__1_444_);
v___x_463_ = lean_box(0);
v___x_464_ = lean_apply_1(v_h__7_450_, v___x_463_);
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__1_splitter___redArg___boxed(lean_object* v_op_465_, lean_object* v_h__1_466_, lean_object* v_h__2_467_, lean_object* v_h__3_468_, lean_object* v_h__4_469_, lean_object* v_h__5_470_, lean_object* v_h__6_471_, lean_object* v_h__7_472_){
_start:
{
uint8_t v_op_76__boxed_473_; lean_object* v_res_474_; 
v_op_76__boxed_473_ = lean_unbox(v_op_465_);
v_res_474_ = lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__1_splitter___redArg(v_op_76__boxed_473_, v_h__1_466_, v_h__2_467_, v_h__3_468_, v_h__4_469_, v_h__5_470_, v_h__6_471_, v_h__7_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__1_splitter(lean_object* v_motive_475_, uint8_t v_op_476_, lean_object* v_h__1_477_, lean_object* v_h__2_478_, lean_object* v_h__3_479_, lean_object* v_h__4_480_, lean_object* v_h__5_481_, lean_object* v_h__6_482_, lean_object* v_h__7_483_){
_start:
{
switch(v_op_476_)
{
case 0:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v_h__7_483_);
lean_dec(v_h__6_482_);
lean_dec(v_h__5_481_);
lean_dec(v_h__4_480_);
lean_dec(v_h__3_479_);
lean_dec(v_h__2_478_);
v___x_484_ = lean_box(0);
v___x_485_ = lean_apply_1(v_h__1_477_, v___x_484_);
return v___x_485_;
}
case 1:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec(v_h__7_483_);
lean_dec(v_h__6_482_);
lean_dec(v_h__5_481_);
lean_dec(v_h__4_480_);
lean_dec(v_h__2_478_);
lean_dec(v_h__1_477_);
v___x_486_ = lean_box(0);
v___x_487_ = lean_apply_1(v_h__3_479_, v___x_486_);
return v___x_487_;
}
case 2:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec(v_h__7_483_);
lean_dec(v_h__6_482_);
lean_dec(v_h__5_481_);
lean_dec(v_h__3_479_);
lean_dec(v_h__2_478_);
lean_dec(v_h__1_477_);
v___x_488_ = lean_box(0);
v___x_489_ = lean_apply_1(v_h__4_480_, v___x_488_);
return v___x_489_;
}
case 3:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec(v_h__7_483_);
lean_dec(v_h__6_482_);
lean_dec(v_h__5_481_);
lean_dec(v_h__4_480_);
lean_dec(v_h__3_479_);
lean_dec(v_h__1_477_);
v___x_490_ = lean_box(0);
v___x_491_ = lean_apply_1(v_h__2_478_, v___x_490_);
return v___x_491_;
}
case 4:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_dec(v_h__7_483_);
lean_dec(v_h__6_482_);
lean_dec(v_h__4_480_);
lean_dec(v_h__3_479_);
lean_dec(v_h__2_478_);
lean_dec(v_h__1_477_);
v___x_492_ = lean_box(0);
v___x_493_ = lean_apply_1(v_h__5_481_, v___x_492_);
return v___x_493_;
}
case 5:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec(v_h__7_483_);
lean_dec(v_h__5_481_);
lean_dec(v_h__4_480_);
lean_dec(v_h__3_479_);
lean_dec(v_h__2_478_);
lean_dec(v_h__1_477_);
v___x_494_ = lean_box(0);
v___x_495_ = lean_apply_1(v_h__6_482_, v___x_494_);
return v___x_495_;
}
default: 
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v_h__6_482_);
lean_dec(v_h__5_481_);
lean_dec(v_h__4_480_);
lean_dec(v_h__3_479_);
lean_dec(v_h__2_478_);
lean_dec(v_h__1_477_);
v___x_496_ = lean_box(0);
v___x_497_ = lean_apply_1(v_h__7_483_, v___x_496_);
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__1_splitter___boxed(lean_object* v_motive_498_, lean_object* v_op_499_, lean_object* v_h__1_500_, lean_object* v_h__2_501_, lean_object* v_h__3_502_, lean_object* v_h__4_503_, lean_object* v_h__5_504_, lean_object* v_h__6_505_, lean_object* v_h__7_506_){
_start:
{
uint8_t v_op_107__boxed_507_; lean_object* v_res_508_; 
v_op_107__boxed_507_ = lean_unbox(v_op_499_);
v_res_508_ = lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__1_splitter(v_motive_498_, v_op_107__boxed_507_, v_h__1_500_, v_h__2_501_, v_h__3_502_, v_h__4_503_, v_h__5_504_, v_h__6_505_, v_h__7_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__6_splitter___redArg(lean_object* v_x_509_, lean_object* v_h__1_510_, lean_object* v_h__2_511_){
_start:
{
if (lean_obj_tag(v_x_509_) == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec(v_h__1_510_);
v___x_512_ = lean_box(0);
v___x_513_ = lean_apply_1(v_h__2_511_, v___x_512_);
return v___x_513_;
}
else
{
lean_object* v_val_514_; lean_object* v___x_515_; 
lean_dec(v_h__2_511_);
v_val_514_ = lean_ctor_get(v_x_509_, 0);
lean_inc(v_val_514_);
lean_dec_ref(v_x_509_);
v___x_515_ = lean_apply_1(v_h__1_510_, v_val_514_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerExp_match__6_splitter(lean_object* v_motive_516_, lean_object* v_x_517_, lean_object* v_h__1_518_, lean_object* v_h__2_519_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v_h__1_518_);
v___x_520_ = lean_box(0);
v___x_521_ = lean_apply_1(v_h__2_519_, v___x_520_);
return v___x_521_;
}
else
{
lean_object* v_val_522_; lean_object* v___x_523_; 
lean_dec(v_h__2_519_);
v_val_522_ = lean_ctor_get(v_x_517_, 0);
lean_inc(v_val_522_);
lean_dec_ref(v_x_517_);
v___x_523_ = lean_apply_1(v_h__1_518_, v_val_522_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__7_splitter___redArg(lean_object* v_x_524_, lean_object* v_h__1_525_, lean_object* v_h__2_526_, lean_object* v_h__3_527_, lean_object* v_h__4_528_, lean_object* v_h__5_529_, lean_object* v_h__6_530_, lean_object* v_h__7_531_, lean_object* v_h__8_532_, lean_object* v_h__9_533_, lean_object* v_h__10_534_){
_start:
{
switch(lean_obj_tag(v_x_524_))
{
case 0:
{
lean_object* v_name_535_; lean_object* v_val_536_; lean_object* v___x_537_; 
lean_dec(v_h__10_534_);
lean_dec(v_h__9_533_);
lean_dec(v_h__8_532_);
lean_dec(v_h__7_531_);
lean_dec(v_h__6_530_);
lean_dec(v_h__5_529_);
lean_dec(v_h__4_528_);
lean_dec(v_h__3_527_);
lean_dec(v_h__2_526_);
v_name_535_ = lean_ctor_get(v_x_524_, 0);
lean_inc_ref(v_name_535_);
v_val_536_ = lean_ctor_get(v_x_524_, 1);
lean_inc(v_val_536_);
lean_dec_ref(v_x_524_);
v___x_537_ = lean_apply_2(v_h__1_525_, v_name_535_, v_val_536_);
return v___x_537_;
}
case 1:
{
lean_object* v_name_538_; lean_object* v_val_539_; lean_object* v___x_540_; 
lean_dec(v_h__10_534_);
lean_dec(v_h__9_533_);
lean_dec(v_h__8_532_);
lean_dec(v_h__7_531_);
lean_dec(v_h__6_530_);
lean_dec(v_h__5_529_);
lean_dec(v_h__4_528_);
lean_dec(v_h__3_527_);
lean_dec(v_h__1_525_);
v_name_538_ = lean_ctor_get(v_x_524_, 0);
lean_inc_ref(v_name_538_);
v_val_539_ = lean_ctor_get(v_x_524_, 1);
lean_inc(v_val_539_);
lean_dec_ref(v_x_524_);
v___x_540_ = lean_apply_2(v_h__2_526_, v_name_538_, v_val_539_);
return v___x_540_;
}
case 2:
{
lean_object* v_addr_541_; lean_object* v_val_542_; lean_object* v___x_543_; 
lean_dec(v_h__10_534_);
lean_dec(v_h__9_533_);
lean_dec(v_h__8_532_);
lean_dec(v_h__7_531_);
lean_dec(v_h__6_530_);
lean_dec(v_h__5_529_);
lean_dec(v_h__4_528_);
lean_dec(v_h__2_526_);
lean_dec(v_h__1_525_);
v_addr_541_ = lean_ctor_get(v_x_524_, 0);
lean_inc(v_addr_541_);
v_val_542_ = lean_ctor_get(v_x_524_, 1);
lean_inc(v_val_542_);
lean_dec_ref(v_x_524_);
v___x_543_ = lean_apply_2(v_h__3_527_, v_addr_541_, v_val_542_);
return v___x_543_;
}
case 3:
{
lean_object* v_addr_544_; lean_object* v_val_545_; lean_object* v___x_546_; 
lean_dec(v_h__10_534_);
lean_dec(v_h__9_533_);
lean_dec(v_h__8_532_);
lean_dec(v_h__7_531_);
lean_dec(v_h__6_530_);
lean_dec(v_h__5_529_);
lean_dec(v_h__3_527_);
lean_dec(v_h__2_526_);
lean_dec(v_h__1_525_);
v_addr_544_ = lean_ctor_get(v_x_524_, 0);
lean_inc(v_addr_544_);
v_val_545_ = lean_ctor_get(v_x_524_, 1);
lean_inc(v_val_545_);
lean_dec_ref(v_x_524_);
v___x_546_ = lean_apply_2(v_h__4_528_, v_addr_544_, v_val_545_);
return v___x_546_;
}
case 4:
{
lean_object* v_args_547_; 
lean_dec(v_h__10_534_);
lean_dec(v_h__9_533_);
lean_dec(v_h__8_532_);
lean_dec(v_h__7_531_);
lean_dec(v_h__4_528_);
lean_dec(v_h__3_527_);
lean_dec(v_h__2_526_);
lean_dec(v_h__1_525_);
v_args_547_ = lean_ctor_get(v_x_524_, 1);
lean_inc(v_args_547_);
if (lean_obj_tag(v_args_547_) == 1)
{
lean_object* v_tail_548_; 
v_tail_548_ = lean_ctor_get(v_args_547_, 1);
if (lean_obj_tag(v_tail_548_) == 1)
{
lean_object* v_tail_549_; 
v_tail_549_ = lean_ctor_get(v_tail_548_, 1);
if (lean_obj_tag(v_tail_549_) == 1)
{
lean_object* v_tail_550_; 
v_tail_550_ = lean_ctor_get(v_tail_549_, 1);
if (lean_obj_tag(v_tail_550_) == 1)
{
lean_object* v_name_551_; lean_object* v_head_552_; lean_object* v_head_553_; lean_object* v_head_554_; lean_object* v_head_555_; lean_object* v_tail_556_; lean_object* v___x_557_; 
lean_inc_ref(v_tail_550_);
lean_inc_ref(v_tail_549_);
lean_inc_ref(v_tail_548_);
lean_dec(v_h__6_530_);
v_name_551_ = lean_ctor_get(v_x_524_, 0);
lean_inc_ref(v_name_551_);
lean_dec_ref(v_x_524_);
v_head_552_ = lean_ctor_get(v_args_547_, 0);
lean_inc(v_head_552_);
lean_dec_ref(v_args_547_);
v_head_553_ = lean_ctor_get(v_tail_548_, 0);
lean_inc(v_head_553_);
lean_dec_ref(v_tail_548_);
v_head_554_ = lean_ctor_get(v_tail_549_, 0);
lean_inc(v_head_554_);
lean_dec_ref(v_tail_549_);
v_head_555_ = lean_ctor_get(v_tail_550_, 0);
lean_inc(v_head_555_);
v_tail_556_ = lean_ctor_get(v_tail_550_, 1);
lean_inc(v_tail_556_);
lean_dec_ref(v_tail_550_);
v___x_557_ = lean_apply_6(v_h__5_529_, v_name_551_, v_head_552_, v_head_553_, v_head_554_, v_head_555_, v_tail_556_);
return v___x_557_;
}
else
{
lean_object* v_name_558_; lean_object* v___x_559_; 
lean_dec(v_h__5_529_);
v_name_558_ = lean_ctor_get(v_x_524_, 0);
lean_inc_ref(v_name_558_);
lean_dec_ref(v_x_524_);
v___x_559_ = lean_apply_3(v_h__6_530_, v_name_558_, v_args_547_, lean_box(0));
return v___x_559_;
}
}
else
{
lean_object* v_name_560_; lean_object* v___x_561_; 
lean_dec(v_h__5_529_);
v_name_560_ = lean_ctor_get(v_x_524_, 0);
lean_inc_ref(v_name_560_);
lean_dec_ref(v_x_524_);
v___x_561_ = lean_apply_3(v_h__6_530_, v_name_560_, v_args_547_, lean_box(0));
return v___x_561_;
}
}
else
{
lean_object* v_name_562_; lean_object* v___x_563_; 
lean_dec(v_h__5_529_);
v_name_562_ = lean_ctor_get(v_x_524_, 0);
lean_inc_ref(v_name_562_);
lean_dec_ref(v_x_524_);
v___x_563_ = lean_apply_3(v_h__6_530_, v_name_562_, v_args_547_, lean_box(0));
return v___x_563_;
}
}
else
{
lean_object* v_name_564_; lean_object* v___x_565_; 
lean_dec(v_h__5_529_);
v_name_564_ = lean_ctor_get(v_x_524_, 0);
lean_inc_ref(v_name_564_);
lean_dec_ref(v_x_524_);
v___x_565_ = lean_apply_3(v_h__6_530_, v_name_564_, v_args_547_, lean_box(0));
return v___x_565_;
}
}
case 5:
{
lean_object* v_ret_566_; lean_object* v_fn_567_; lean_object* v_args_568_; lean_object* v___x_569_; 
lean_dec(v_h__10_534_);
lean_dec(v_h__9_533_);
lean_dec(v_h__8_532_);
lean_dec(v_h__6_530_);
lean_dec(v_h__5_529_);
lean_dec(v_h__4_528_);
lean_dec(v_h__3_527_);
lean_dec(v_h__2_526_);
lean_dec(v_h__1_525_);
v_ret_566_ = lean_ctor_get(v_x_524_, 0);
lean_inc_ref(v_ret_566_);
v_fn_567_ = lean_ctor_get(v_x_524_, 1);
lean_inc_ref(v_fn_567_);
v_args_568_ = lean_ctor_get(v_x_524_, 2);
lean_inc(v_args_568_);
lean_dec_ref(v_x_524_);
v___x_569_ = lean_apply_3(v_h__7_531_, v_ret_566_, v_fn_567_, v_args_568_);
return v___x_569_;
}
case 6:
{
lean_object* v_val_570_; lean_object* v___x_571_; 
lean_dec(v_h__10_534_);
lean_dec(v_h__9_533_);
lean_dec(v_h__7_531_);
lean_dec(v_h__6_530_);
lean_dec(v_h__5_529_);
lean_dec(v_h__4_528_);
lean_dec(v_h__3_527_);
lean_dec(v_h__2_526_);
lean_dec(v_h__1_525_);
v_val_570_ = lean_ctor_get(v_x_524_, 0);
lean_inc(v_val_570_);
lean_dec_ref(v_x_524_);
v___x_571_ = lean_apply_1(v_h__8_532_, v_val_570_);
return v___x_571_;
}
case 7:
{
lean_object* v_cond_572_; lean_object* v_thn_573_; lean_object* v_els_574_; lean_object* v___x_575_; 
lean_dec(v_h__10_534_);
lean_dec(v_h__8_532_);
lean_dec(v_h__7_531_);
lean_dec(v_h__6_530_);
lean_dec(v_h__5_529_);
lean_dec(v_h__4_528_);
lean_dec(v_h__3_527_);
lean_dec(v_h__2_526_);
lean_dec(v_h__1_525_);
v_cond_572_ = lean_ctor_get(v_x_524_, 0);
lean_inc(v_cond_572_);
v_thn_573_ = lean_ctor_get(v_x_524_, 1);
lean_inc(v_thn_573_);
v_els_574_ = lean_ctor_get(v_x_524_, 2);
lean_inc(v_els_574_);
lean_dec_ref(v_x_524_);
v___x_575_ = lean_apply_3(v_h__9_533_, v_cond_572_, v_thn_573_, v_els_574_);
return v___x_575_;
}
default: 
{
lean_object* v_cond_576_; lean_object* v_body_577_; lean_object* v___x_578_; 
lean_dec(v_h__9_533_);
lean_dec(v_h__8_532_);
lean_dec(v_h__7_531_);
lean_dec(v_h__6_530_);
lean_dec(v_h__5_529_);
lean_dec(v_h__4_528_);
lean_dec(v_h__3_527_);
lean_dec(v_h__2_526_);
lean_dec(v_h__1_525_);
v_cond_576_ = lean_ctor_get(v_x_524_, 0);
lean_inc(v_cond_576_);
v_body_577_ = lean_ctor_get(v_x_524_, 1);
lean_inc(v_body_577_);
lean_dec_ref(v_x_524_);
v___x_578_ = lean_apply_2(v_h__10_534_, v_cond_576_, v_body_577_);
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__7_splitter(lean_object* v_motive_579_, lean_object* v_x_580_, lean_object* v_h__1_581_, lean_object* v_h__2_582_, lean_object* v_h__3_583_, lean_object* v_h__4_584_, lean_object* v_h__5_585_, lean_object* v_h__6_586_, lean_object* v_h__7_587_, lean_object* v_h__8_588_, lean_object* v_h__9_589_, lean_object* v_h__10_590_){
_start:
{
switch(lean_obj_tag(v_x_580_))
{
case 0:
{
lean_object* v_name_591_; lean_object* v_val_592_; lean_object* v___x_593_; 
lean_dec(v_h__10_590_);
lean_dec(v_h__9_589_);
lean_dec(v_h__8_588_);
lean_dec(v_h__7_587_);
lean_dec(v_h__6_586_);
lean_dec(v_h__5_585_);
lean_dec(v_h__4_584_);
lean_dec(v_h__3_583_);
lean_dec(v_h__2_582_);
v_name_591_ = lean_ctor_get(v_x_580_, 0);
lean_inc_ref(v_name_591_);
v_val_592_ = lean_ctor_get(v_x_580_, 1);
lean_inc(v_val_592_);
lean_dec_ref(v_x_580_);
v___x_593_ = lean_apply_2(v_h__1_581_, v_name_591_, v_val_592_);
return v___x_593_;
}
case 1:
{
lean_object* v_name_594_; lean_object* v_val_595_; lean_object* v___x_596_; 
lean_dec(v_h__10_590_);
lean_dec(v_h__9_589_);
lean_dec(v_h__8_588_);
lean_dec(v_h__7_587_);
lean_dec(v_h__6_586_);
lean_dec(v_h__5_585_);
lean_dec(v_h__4_584_);
lean_dec(v_h__3_583_);
lean_dec(v_h__1_581_);
v_name_594_ = lean_ctor_get(v_x_580_, 0);
lean_inc_ref(v_name_594_);
v_val_595_ = lean_ctor_get(v_x_580_, 1);
lean_inc(v_val_595_);
lean_dec_ref(v_x_580_);
v___x_596_ = lean_apply_2(v_h__2_582_, v_name_594_, v_val_595_);
return v___x_596_;
}
case 2:
{
lean_object* v_addr_597_; lean_object* v_val_598_; lean_object* v___x_599_; 
lean_dec(v_h__10_590_);
lean_dec(v_h__9_589_);
lean_dec(v_h__8_588_);
lean_dec(v_h__7_587_);
lean_dec(v_h__6_586_);
lean_dec(v_h__5_585_);
lean_dec(v_h__4_584_);
lean_dec(v_h__2_582_);
lean_dec(v_h__1_581_);
v_addr_597_ = lean_ctor_get(v_x_580_, 0);
lean_inc(v_addr_597_);
v_val_598_ = lean_ctor_get(v_x_580_, 1);
lean_inc(v_val_598_);
lean_dec_ref(v_x_580_);
v___x_599_ = lean_apply_2(v_h__3_583_, v_addr_597_, v_val_598_);
return v___x_599_;
}
case 3:
{
lean_object* v_addr_600_; lean_object* v_val_601_; lean_object* v___x_602_; 
lean_dec(v_h__10_590_);
lean_dec(v_h__9_589_);
lean_dec(v_h__8_588_);
lean_dec(v_h__7_587_);
lean_dec(v_h__6_586_);
lean_dec(v_h__5_585_);
lean_dec(v_h__3_583_);
lean_dec(v_h__2_582_);
lean_dec(v_h__1_581_);
v_addr_600_ = lean_ctor_get(v_x_580_, 0);
lean_inc(v_addr_600_);
v_val_601_ = lean_ctor_get(v_x_580_, 1);
lean_inc(v_val_601_);
lean_dec_ref(v_x_580_);
v___x_602_ = lean_apply_2(v_h__4_584_, v_addr_600_, v_val_601_);
return v___x_602_;
}
case 4:
{
lean_object* v_args_603_; 
lean_dec(v_h__10_590_);
lean_dec(v_h__9_589_);
lean_dec(v_h__8_588_);
lean_dec(v_h__7_587_);
lean_dec(v_h__4_584_);
lean_dec(v_h__3_583_);
lean_dec(v_h__2_582_);
lean_dec(v_h__1_581_);
v_args_603_ = lean_ctor_get(v_x_580_, 1);
lean_inc(v_args_603_);
if (lean_obj_tag(v_args_603_) == 1)
{
lean_object* v_tail_604_; 
v_tail_604_ = lean_ctor_get(v_args_603_, 1);
if (lean_obj_tag(v_tail_604_) == 1)
{
lean_object* v_tail_605_; 
v_tail_605_ = lean_ctor_get(v_tail_604_, 1);
if (lean_obj_tag(v_tail_605_) == 1)
{
lean_object* v_tail_606_; 
v_tail_606_ = lean_ctor_get(v_tail_605_, 1);
if (lean_obj_tag(v_tail_606_) == 1)
{
lean_object* v_name_607_; lean_object* v_head_608_; lean_object* v_head_609_; lean_object* v_head_610_; lean_object* v_head_611_; lean_object* v_tail_612_; lean_object* v___x_613_; 
lean_inc_ref(v_tail_606_);
lean_inc_ref(v_tail_605_);
lean_inc_ref(v_tail_604_);
lean_dec(v_h__6_586_);
v_name_607_ = lean_ctor_get(v_x_580_, 0);
lean_inc_ref(v_name_607_);
lean_dec_ref(v_x_580_);
v_head_608_ = lean_ctor_get(v_args_603_, 0);
lean_inc(v_head_608_);
lean_dec_ref(v_args_603_);
v_head_609_ = lean_ctor_get(v_tail_604_, 0);
lean_inc(v_head_609_);
lean_dec_ref(v_tail_604_);
v_head_610_ = lean_ctor_get(v_tail_605_, 0);
lean_inc(v_head_610_);
lean_dec_ref(v_tail_605_);
v_head_611_ = lean_ctor_get(v_tail_606_, 0);
lean_inc(v_head_611_);
v_tail_612_ = lean_ctor_get(v_tail_606_, 1);
lean_inc(v_tail_612_);
lean_dec_ref(v_tail_606_);
v___x_613_ = lean_apply_6(v_h__5_585_, v_name_607_, v_head_608_, v_head_609_, v_head_610_, v_head_611_, v_tail_612_);
return v___x_613_;
}
else
{
lean_object* v_name_614_; lean_object* v___x_615_; 
lean_dec(v_h__5_585_);
v_name_614_ = lean_ctor_get(v_x_580_, 0);
lean_inc_ref(v_name_614_);
lean_dec_ref(v_x_580_);
v___x_615_ = lean_apply_3(v_h__6_586_, v_name_614_, v_args_603_, lean_box(0));
return v___x_615_;
}
}
else
{
lean_object* v_name_616_; lean_object* v___x_617_; 
lean_dec(v_h__5_585_);
v_name_616_ = lean_ctor_get(v_x_580_, 0);
lean_inc_ref(v_name_616_);
lean_dec_ref(v_x_580_);
v___x_617_ = lean_apply_3(v_h__6_586_, v_name_616_, v_args_603_, lean_box(0));
return v___x_617_;
}
}
else
{
lean_object* v_name_618_; lean_object* v___x_619_; 
lean_dec(v_h__5_585_);
v_name_618_ = lean_ctor_get(v_x_580_, 0);
lean_inc_ref(v_name_618_);
lean_dec_ref(v_x_580_);
v___x_619_ = lean_apply_3(v_h__6_586_, v_name_618_, v_args_603_, lean_box(0));
return v___x_619_;
}
}
else
{
lean_object* v_name_620_; lean_object* v___x_621_; 
lean_dec(v_h__5_585_);
v_name_620_ = lean_ctor_get(v_x_580_, 0);
lean_inc_ref(v_name_620_);
lean_dec_ref(v_x_580_);
v___x_621_ = lean_apply_3(v_h__6_586_, v_name_620_, v_args_603_, lean_box(0));
return v___x_621_;
}
}
case 5:
{
lean_object* v_ret_622_; lean_object* v_fn_623_; lean_object* v_args_624_; lean_object* v___x_625_; 
lean_dec(v_h__10_590_);
lean_dec(v_h__9_589_);
lean_dec(v_h__8_588_);
lean_dec(v_h__6_586_);
lean_dec(v_h__5_585_);
lean_dec(v_h__4_584_);
lean_dec(v_h__3_583_);
lean_dec(v_h__2_582_);
lean_dec(v_h__1_581_);
v_ret_622_ = lean_ctor_get(v_x_580_, 0);
lean_inc_ref(v_ret_622_);
v_fn_623_ = lean_ctor_get(v_x_580_, 1);
lean_inc_ref(v_fn_623_);
v_args_624_ = lean_ctor_get(v_x_580_, 2);
lean_inc(v_args_624_);
lean_dec_ref(v_x_580_);
v___x_625_ = lean_apply_3(v_h__7_587_, v_ret_622_, v_fn_623_, v_args_624_);
return v___x_625_;
}
case 6:
{
lean_object* v_val_626_; lean_object* v___x_627_; 
lean_dec(v_h__10_590_);
lean_dec(v_h__9_589_);
lean_dec(v_h__7_587_);
lean_dec(v_h__6_586_);
lean_dec(v_h__5_585_);
lean_dec(v_h__4_584_);
lean_dec(v_h__3_583_);
lean_dec(v_h__2_582_);
lean_dec(v_h__1_581_);
v_val_626_ = lean_ctor_get(v_x_580_, 0);
lean_inc(v_val_626_);
lean_dec_ref(v_x_580_);
v___x_627_ = lean_apply_1(v_h__8_588_, v_val_626_);
return v___x_627_;
}
case 7:
{
lean_object* v_cond_628_; lean_object* v_thn_629_; lean_object* v_els_630_; lean_object* v___x_631_; 
lean_dec(v_h__10_590_);
lean_dec(v_h__8_588_);
lean_dec(v_h__7_587_);
lean_dec(v_h__6_586_);
lean_dec(v_h__5_585_);
lean_dec(v_h__4_584_);
lean_dec(v_h__3_583_);
lean_dec(v_h__2_582_);
lean_dec(v_h__1_581_);
v_cond_628_ = lean_ctor_get(v_x_580_, 0);
lean_inc(v_cond_628_);
v_thn_629_ = lean_ctor_get(v_x_580_, 1);
lean_inc(v_thn_629_);
v_els_630_ = lean_ctor_get(v_x_580_, 2);
lean_inc(v_els_630_);
lean_dec_ref(v_x_580_);
v___x_631_ = lean_apply_3(v_h__9_589_, v_cond_628_, v_thn_629_, v_els_630_);
return v___x_631_;
}
default: 
{
lean_object* v_cond_632_; lean_object* v_body_633_; lean_object* v___x_634_; 
lean_dec(v_h__9_589_);
lean_dec(v_h__8_588_);
lean_dec(v_h__7_587_);
lean_dec(v_h__6_586_);
lean_dec(v_h__5_585_);
lean_dec(v_h__4_584_);
lean_dec(v_h__3_583_);
lean_dec(v_h__2_582_);
lean_dec(v_h__1_581_);
v_cond_632_ = lean_ctor_get(v_x_580_, 0);
lean_inc(v_cond_632_);
v_body_633_ = lean_ctor_get(v_x_580_, 1);
lean_inc(v_body_633_);
lean_dec_ref(v_x_580_);
v___x_634_ = lean_apply_2(v_h__10_590_, v_cond_632_, v_body_633_);
return v___x_634_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__1_splitter___redArg(lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_h__1_639_, lean_object* v_h__2_640_){
_start:
{
if (lean_obj_tag(v_x_635_) == 1)
{
if (lean_obj_tag(v_x_636_) == 1)
{
if (lean_obj_tag(v_x_637_) == 1)
{
if (lean_obj_tag(v_x_638_) == 1)
{
lean_object* v_val_641_; lean_object* v_val_642_; lean_object* v_val_643_; lean_object* v_val_644_; lean_object* v___x_645_; 
lean_dec(v_h__2_640_);
v_val_641_ = lean_ctor_get(v_x_635_, 0);
lean_inc(v_val_641_);
lean_dec_ref(v_x_635_);
v_val_642_ = lean_ctor_get(v_x_636_, 0);
lean_inc(v_val_642_);
lean_dec_ref(v_x_636_);
v_val_643_ = lean_ctor_get(v_x_637_, 0);
lean_inc(v_val_643_);
lean_dec_ref(v_x_637_);
v_val_644_ = lean_ctor_get(v_x_638_, 0);
lean_inc(v_val_644_);
lean_dec_ref(v_x_638_);
v___x_645_ = lean_apply_4(v_h__1_639_, v_val_641_, v_val_642_, v_val_643_, v_val_644_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; 
lean_dec(v_h__1_639_);
v___x_646_ = lean_apply_5(v_h__2_640_, v_x_635_, v_x_636_, v_x_637_, v_x_638_, lean_box(0));
return v___x_646_;
}
}
else
{
lean_object* v___x_647_; 
lean_dec(v_h__1_639_);
v___x_647_ = lean_apply_5(v_h__2_640_, v_x_635_, v_x_636_, v_x_637_, v_x_638_, lean_box(0));
return v___x_647_;
}
}
else
{
lean_object* v___x_648_; 
lean_dec(v_h__1_639_);
v___x_648_ = lean_apply_5(v_h__2_640_, v_x_635_, v_x_636_, v_x_637_, v_x_638_, lean_box(0));
return v___x_648_;
}
}
else
{
lean_object* v___x_649_; 
lean_dec(v_h__1_639_);
v___x_649_ = lean_apply_5(v_h__2_640_, v_x_635_, v_x_636_, v_x_637_, v_x_638_, lean_box(0));
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__1_splitter(lean_object* v_motive_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_h__1_655_, lean_object* v_h__2_656_){
_start:
{
if (lean_obj_tag(v_x_651_) == 1)
{
if (lean_obj_tag(v_x_652_) == 1)
{
if (lean_obj_tag(v_x_653_) == 1)
{
if (lean_obj_tag(v_x_654_) == 1)
{
lean_object* v_val_657_; lean_object* v_val_658_; lean_object* v_val_659_; lean_object* v_val_660_; lean_object* v___x_661_; 
lean_dec(v_h__2_656_);
v_val_657_ = lean_ctor_get(v_x_651_, 0);
lean_inc(v_val_657_);
lean_dec_ref(v_x_651_);
v_val_658_ = lean_ctor_get(v_x_652_, 0);
lean_inc(v_val_658_);
lean_dec_ref(v_x_652_);
v_val_659_ = lean_ctor_get(v_x_653_, 0);
lean_inc(v_val_659_);
lean_dec_ref(v_x_653_);
v_val_660_ = lean_ctor_get(v_x_654_, 0);
lean_inc(v_val_660_);
lean_dec_ref(v_x_654_);
v___x_661_ = lean_apply_4(v_h__1_655_, v_val_657_, v_val_658_, v_val_659_, v_val_660_);
return v___x_661_;
}
else
{
lean_object* v___x_662_; 
lean_dec(v_h__1_655_);
v___x_662_ = lean_apply_5(v_h__2_656_, v_x_651_, v_x_652_, v_x_653_, v_x_654_, lean_box(0));
return v___x_662_;
}
}
else
{
lean_object* v___x_663_; 
lean_dec(v_h__1_655_);
v___x_663_ = lean_apply_5(v_h__2_656_, v_x_651_, v_x_652_, v_x_653_, v_x_654_, lean_box(0));
return v___x_663_;
}
}
else
{
lean_object* v___x_664_; 
lean_dec(v_h__1_655_);
v___x_664_ = lean_apply_5(v_h__2_656_, v_x_651_, v_x_652_, v_x_653_, v_x_654_, lean_box(0));
return v___x_664_;
}
}
else
{
lean_object* v___x_665_; 
lean_dec(v_h__1_655_);
v___x_665_ = lean_apply_5(v_h__2_656_, v_x_651_, v_x_652_, v_x_653_, v_x_654_, lean_box(0));
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__3_splitter___redArg(lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_x_668_, lean_object* v_h__1_669_, lean_object* v_h__2_670_){
_start:
{
if (lean_obj_tag(v_x_666_) == 1)
{
if (lean_obj_tag(v_x_667_) == 1)
{
if (lean_obj_tag(v_x_668_) == 1)
{
lean_object* v_val_671_; lean_object* v_val_672_; lean_object* v_val_673_; lean_object* v___x_674_; 
lean_dec(v_h__2_670_);
v_val_671_ = lean_ctor_get(v_x_666_, 0);
lean_inc(v_val_671_);
lean_dec_ref(v_x_666_);
v_val_672_ = lean_ctor_get(v_x_667_, 0);
lean_inc(v_val_672_);
lean_dec_ref(v_x_667_);
v_val_673_ = lean_ctor_get(v_x_668_, 0);
lean_inc(v_val_673_);
lean_dec_ref(v_x_668_);
v___x_674_ = lean_apply_3(v_h__1_669_, v_val_671_, v_val_672_, v_val_673_);
return v___x_674_;
}
else
{
lean_object* v___x_675_; 
lean_dec(v_h__1_669_);
v___x_675_ = lean_apply_4(v_h__2_670_, v_x_666_, v_x_667_, v_x_668_, lean_box(0));
return v___x_675_;
}
}
else
{
lean_object* v___x_676_; 
lean_dec(v_h__1_669_);
v___x_676_ = lean_apply_4(v_h__2_670_, v_x_666_, v_x_667_, v_x_668_, lean_box(0));
return v___x_676_;
}
}
else
{
lean_object* v___x_677_; 
lean_dec(v_h__1_669_);
v___x_677_ = lean_apply_4(v_h__2_670_, v_x_666_, v_x_667_, v_x_668_, lean_box(0));
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__3_splitter(lean_object* v_motive_678_, lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_h__1_682_, lean_object* v_h__2_683_){
_start:
{
if (lean_obj_tag(v_x_679_) == 1)
{
if (lean_obj_tag(v_x_680_) == 1)
{
if (lean_obj_tag(v_x_681_) == 1)
{
lean_object* v_val_684_; lean_object* v_val_685_; lean_object* v_val_686_; lean_object* v___x_687_; 
lean_dec(v_h__2_683_);
v_val_684_ = lean_ctor_get(v_x_679_, 0);
lean_inc(v_val_684_);
lean_dec_ref(v_x_679_);
v_val_685_ = lean_ctor_get(v_x_680_, 0);
lean_inc(v_val_685_);
lean_dec_ref(v_x_680_);
v_val_686_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_val_686_);
lean_dec_ref(v_x_681_);
v___x_687_ = lean_apply_3(v_h__1_682_, v_val_684_, v_val_685_, v_val_686_);
return v___x_687_;
}
else
{
lean_object* v___x_688_; 
lean_dec(v_h__1_682_);
v___x_688_ = lean_apply_4(v_h__2_683_, v_x_679_, v_x_680_, v_x_681_, lean_box(0));
return v___x_688_;
}
}
else
{
lean_object* v___x_689_; 
lean_dec(v_h__1_682_);
v___x_689_ = lean_apply_4(v_h__2_683_, v_x_679_, v_x_680_, v_x_681_, lean_box(0));
return v___x_689_;
}
}
else
{
lean_object* v___x_690_; 
lean_dec(v_h__1_682_);
v___x_690_ = lean_apply_4(v_h__2_683_, v_x_679_, v_x_680_, v_x_681_, lean_box(0));
return v___x_690_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__5_splitter___redArg(lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_h__1_693_, lean_object* v_h__2_694_){
_start:
{
if (lean_obj_tag(v_x_691_) == 1)
{
if (lean_obj_tag(v_x_692_) == 1)
{
lean_object* v_val_695_; lean_object* v_val_696_; lean_object* v___x_697_; 
lean_dec(v_h__2_694_);
v_val_695_ = lean_ctor_get(v_x_691_, 0);
lean_inc(v_val_695_);
lean_dec_ref(v_x_691_);
v_val_696_ = lean_ctor_get(v_x_692_, 0);
lean_inc(v_val_696_);
lean_dec_ref(v_x_692_);
v___x_697_ = lean_apply_2(v_h__1_693_, v_val_695_, v_val_696_);
return v___x_697_;
}
else
{
lean_object* v___x_698_; 
lean_dec(v_h__1_693_);
v___x_698_ = lean_apply_3(v_h__2_694_, v_x_691_, v_x_692_, lean_box(0));
return v___x_698_;
}
}
else
{
lean_object* v___x_699_; 
lean_dec(v_h__1_693_);
v___x_699_ = lean_apply_3(v_h__2_694_, v_x_691_, v_x_692_, lean_box(0));
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Lower_0__Pancake_Lower_lowerStmt1_match__5_splitter(lean_object* v_motive_700_, lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_h__1_703_, lean_object* v_h__2_704_){
_start:
{
if (lean_obj_tag(v_x_701_) == 1)
{
if (lean_obj_tag(v_x_702_) == 1)
{
lean_object* v_val_705_; lean_object* v_val_706_; lean_object* v___x_707_; 
lean_dec(v_h__2_704_);
v_val_705_ = lean_ctor_get(v_x_701_, 0);
lean_inc(v_val_705_);
lean_dec_ref(v_x_701_);
v_val_706_ = lean_ctor_get(v_x_702_, 0);
lean_inc(v_val_706_);
lean_dec_ref(v_x_702_);
v___x_707_ = lean_apply_2(v_h__1_703_, v_val_705_, v_val_706_);
return v___x_707_;
}
else
{
lean_object* v___x_708_; 
lean_dec(v_h__1_703_);
v___x_708_ = lean_apply_3(v_h__2_704_, v_x_701_, v_x_702_, lean_box(0));
return v___x_708_;
}
}
else
{
lean_object* v___x_709_; 
lean_dec(v_h__1_703_);
v___x_709_ = lean_apply_3(v_h__2_704_, v_x_701_, v_x_702_, lean_box(0));
return v___x_709_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_Sem(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Dsl_EmitPancake(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_Lower(uint8_t builtin) {
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
res = initialize_orb_x2dcompiler_Dsl_EmitPancake(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Pancake_Lower_regionProg = _init_lp_orb_x2dcompiler_Pancake_Lower_regionProg();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_Lower_regionProg);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
