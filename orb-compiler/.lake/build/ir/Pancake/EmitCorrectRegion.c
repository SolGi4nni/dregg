// Lean compiler output
// Module: Pancake.EmitCorrectRegion
// Imports: public import Init public meta import Init public import Pancake.Sem public import Pancake.Lower
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_step(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_step___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanFrom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundScan(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundScan___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_c0Encode(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_c0Encode___boxed(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "alen"};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "off"};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "len"};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__4_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__3_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__1_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__6_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__7_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__8_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__10;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__11;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__12;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_EmitCorrectRegion_0__Pancake_EmitCorrect_c0Encode_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_EmitCorrectRegion_0__Pancake_EmitCorrect_c0Encode_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_EmitCorrectRegion_0__Pancake_EmitCorrect_scanFrom_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_EmitCorrectRegion_0__Pancake_EmitCorrect_scanFrom_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_EmitCorrectRegion_0__Pancake_EmitCorrect_scanFrom_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_EmitCorrectRegion_0__Pancake_EmitCorrect_scanFrom_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "acc"};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__4;
static const lean_string_object lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "buf"};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__6_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__7_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__7_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__9_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__10_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__10_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__11_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__12;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__13;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__14;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__15;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__16;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__17;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__18;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__19;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__20;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__21;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__9_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__1;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__8_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__1_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__5;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_step(lean_object* v_acc_1_, lean_object* v_b_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_3_ = lean_unsigned_to_nat(31u);
v___x_4_ = lean_nat_mul(v_acc_1_, v___x_3_);
v___x_5_ = lean_nat_add(v___x_4_, v_b_2_);
lean_dec(v___x_4_);
v___x_6_ = lean_unsigned_to_nat(16777216u);
v___x_7_ = lean_nat_mod(v___x_5_, v___x_6_);
lean_dec(v___x_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_step___boxed(lean_object* v_acc_8_, lean_object* v_b_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_orb_x2dcompiler_Pancake_EmitCorrect_step(v_acc_8_, v_b_9_);
lean_dec(v_b_9_);
lean_dec(v_acc_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanFrom(lean_object* v_a_11_, lean_object* v_off_12_, lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
lean_object* v_zero_15_; uint8_t v_isZero_16_; 
v_zero_15_ = lean_unsigned_to_nat(0u);
v_isZero_16_ = lean_nat_dec_eq(v_x_13_, v_zero_15_);
if (v_isZero_16_ == 1)
{
lean_dec(v_x_13_);
lean_dec(v_off_12_);
return v_x_14_;
}
else
{
lean_object* v_one_17_; lean_object* v_n_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_one_17_ = lean_unsigned_to_nat(1u);
v_n_18_ = lean_nat_sub(v_x_13_, v_one_17_);
lean_dec(v_x_13_);
v___x_19_ = lean_nat_add(v_off_12_, v_one_17_);
v___x_20_ = l_List_get_x21Internal___redArg(v_zero_15_, v_a_11_, v_off_12_);
v___x_21_ = lp_orb_x2dcompiler_Pancake_EmitCorrect_step(v_x_14_, v___x_20_);
lean_dec(v___x_20_);
lean_dec(v_x_14_);
v_off_12_ = v___x_19_;
v_x_13_ = v_n_18_;
v_x_14_ = v___x_21_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanFrom___boxed(lean_object* v_a_23_, lean_object* v_off_24_, lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_orb_x2dcompiler_Pancake_EmitCorrect_scanFrom(v_a_23_, v_off_24_, v_x_25_, v_x_26_);
lean_dec(v_a_23_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundScan(lean_object* v_a_28_, lean_object* v_off_29_, lean_object* v_len_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_31_ = lean_nat_add(v_off_29_, v_len_30_);
v___x_32_ = l_List_lengthTR___redArg(v_a_28_);
v___x_33_ = lean_nat_dec_le(v___x_31_, v___x_32_);
lean_dec(v___x_32_);
lean_dec(v___x_31_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
lean_dec(v_len_30_);
lean_dec(v_off_29_);
v___x_34_ = lean_box(0);
return v___x_34_;
}
else
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = lp_orb_x2dcompiler_Pancake_EmitCorrect_scanFrom(v_a_28_, v_off_29_, v_len_30_, v___x_35_);
v___x_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_boundScan___boxed(lean_object* v_a_38_, lean_object* v_off_39_, lean_object* v_len_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_orb_x2dcompiler_Pancake_EmitCorrect_boundScan(v_a_38_, v_off_39_, v_len_40_);
lean_dec(v_a_38_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_c0Encode(lean_object* v_x_42_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
lean_object* v___x_43_; 
v___x_43_ = lean_unsigned_to_nat(4294967295u);
return v___x_43_;
}
else
{
lean_object* v_val_44_; 
v_val_44_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_val_44_);
return v_val_44_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_c0Encode___boxed(lean_object* v_x_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_orb_x2dcompiler_Pancake_EmitCorrect_c0Encode(v_x_45_);
lean_dec(v_x_45_);
return v_res_46_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__9(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_unsigned_to_nat(4294967295u);
v___x_66_ = lean_unsigned_to_nat(64u);
v___x_67_ = l_BitVec_ofNat(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__10(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__9, &lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__9);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__11(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__10, &lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__10);
v___x_71_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__8));
v___x_72_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__12(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = lean_box(0);
v___x_74_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__11, &lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__11);
v___x_75_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__7));
v___x_76_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_73_);
return v___x_76_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__12, &lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk___closed__12);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_EmitCorrectRegion_0__Pancake_EmitCorrect_c0Encode_match__1_splitter___redArg(lean_object* v_x_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_h__2_80_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_apply_1(v_h__1_79_, v___x_81_);
return v___x_82_;
}
else
{
lean_object* v_val_83_; lean_object* v___x_84_; 
lean_dec(v_h__1_79_);
v_val_83_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_val_83_);
lean_dec_ref(v_x_78_);
v___x_84_ = lean_apply_1(v_h__2_80_, v_val_83_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_EmitCorrectRegion_0__Pancake_EmitCorrect_c0Encode_match__1_splitter(lean_object* v_motive_85_, lean_object* v_x_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec(v_h__2_88_);
v___x_89_ = lean_box(0);
v___x_90_ = lean_apply_1(v_h__1_87_, v___x_89_);
return v___x_90_;
}
else
{
lean_object* v_val_91_; lean_object* v___x_92_; 
lean_dec(v_h__1_87_);
v_val_91_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_val_91_);
lean_dec_ref(v_x_86_);
v___x_92_ = lean_apply_1(v_h__2_88_, v_val_91_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_EmitCorrectRegion_0__Pancake_EmitCorrect_scanFrom_match__1_splitter___redArg(lean_object* v_x_93_, lean_object* v_x_94_, lean_object* v_h__1_95_, lean_object* v_h__2_96_){
_start:
{
lean_object* v_zero_97_; uint8_t v_isZero_98_; 
v_zero_97_ = lean_unsigned_to_nat(0u);
v_isZero_98_ = lean_nat_dec_eq(v_x_93_, v_zero_97_);
if (v_isZero_98_ == 1)
{
lean_object* v___x_99_; 
lean_dec(v_h__2_96_);
v___x_99_ = lean_apply_1(v_h__1_95_, v_x_94_);
return v___x_99_;
}
else
{
lean_object* v_one_100_; lean_object* v_n_101_; lean_object* v___x_102_; 
lean_dec(v_h__1_95_);
v_one_100_ = lean_unsigned_to_nat(1u);
v_n_101_ = lean_nat_sub(v_x_93_, v_one_100_);
v___x_102_ = lean_apply_2(v_h__2_96_, v_n_101_, v_x_94_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_EmitCorrectRegion_0__Pancake_EmitCorrect_scanFrom_match__1_splitter___redArg___boxed(lean_object* v_x_103_, lean_object* v_x_104_, lean_object* v_h__1_105_, lean_object* v_h__2_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = lp_orb_x2dcompiler___private_Pancake_EmitCorrectRegion_0__Pancake_EmitCorrect_scanFrom_match__1_splitter___redArg(v_x_103_, v_x_104_, v_h__1_105_, v_h__2_106_);
lean_dec(v_x_103_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_EmitCorrectRegion_0__Pancake_EmitCorrect_scanFrom_match__1_splitter(lean_object* v_motive_108_, lean_object* v_x_109_, lean_object* v_x_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_){
_start:
{
lean_object* v_zero_113_; uint8_t v_isZero_114_; 
v_zero_113_ = lean_unsigned_to_nat(0u);
v_isZero_114_ = lean_nat_dec_eq(v_x_109_, v_zero_113_);
if (v_isZero_114_ == 1)
{
lean_object* v___x_115_; 
lean_dec(v_h__2_112_);
v___x_115_ = lean_apply_1(v_h__1_111_, v_x_110_);
return v___x_115_;
}
else
{
lean_object* v_one_116_; lean_object* v_n_117_; lean_object* v___x_118_; 
lean_dec(v_h__1_111_);
v_one_116_ = lean_unsigned_to_nat(1u);
v_n_117_ = lean_nat_sub(v_x_109_, v_one_116_);
v___x_118_ = lean_apply_2(v_h__2_112_, v_n_117_, v_x_110_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_EmitCorrectRegion_0__Pancake_EmitCorrect_scanFrom_match__1_splitter___boxed(lean_object* v_motive_119_, lean_object* v_x_120_, lean_object* v_x_121_, lean_object* v_h__1_122_, lean_object* v_h__2_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = lp_orb_x2dcompiler___private_Pancake_EmitCorrectRegion_0__Pancake_EmitCorrect_scanFrom_match__1_splitter(v_motive_119_, v_x_120_, v_x_121_, v_h__1_122_, v_h__2_123_);
lean_dec(v_x_120_);
return v_res_124_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__2(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_unsigned_to_nat(31u);
v___x_129_ = lean_unsigned_to_nat(64u);
v___x_130_ = l_BitVec_ofNat(v___x_129_, v___x_128_);
return v___x_130_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__3(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__2, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__2);
v___x_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__4(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__3, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__3);
v___x_134_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__1));
v___x_135_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__12(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; 
v___x_152_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__11));
v___x_153_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__4, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__4);
v___x_154_ = 0;
v___x_155_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set(v___x_155_, 1, v___x_152_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*2, v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__13(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_unsigned_to_nat(16777215u);
v___x_157_ = lean_unsigned_to_nat(64u);
v___x_158_ = l_BitVec_ofNat(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__14(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__13, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__13_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__13);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__15(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; lean_object* v___x_164_; 
v___x_161_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__14, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__14_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__14);
v___x_162_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__12, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__12);
v___x_163_ = 1;
v___x_164_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set(v___x_164_, 1, v___x_161_);
lean_ctor_set_uint8(v___x_164_, sizeof(void*)*2, v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__16(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__15, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__15_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__15);
v___x_166_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__0));
v___x_167_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__17(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_unsigned_to_nat(1u);
v___x_169_ = lean_unsigned_to_nat(64u);
v___x_170_ = l_BitVec_ofNat(v___x_169_, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__18(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__17, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__17_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__17);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__19(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; lean_object* v___x_176_; 
v___x_173_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__18, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__18_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__18);
v___x_174_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__9));
v___x_175_ = 0;
v___x_176_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set(v___x_176_, 1, v___x_173_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*2, v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__20(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__19, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__19_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__19);
v___x_178_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__8));
v___x_179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__21(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__20, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__20_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__20);
v___x_181_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__16, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__16_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__16);
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody(void){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__21, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__21_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__21);
return v___x_183_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile___closed__1(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody;
v___x_189_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile___closed__0));
v___x_190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v___x_188_);
return v___x_190_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile___closed__1, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile___closed__1);
return v___x_191_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__0(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_unsigned_to_nat(64u);
v___x_194_ = l_BitVec_ofNat(v___x_193_, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__1(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__0, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__0);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__3(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__2));
v___x_201_ = lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile;
v___x_202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_200_);
return v___x_202_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__4(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_203_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__3, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__3);
v___x_204_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__1, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__1);
v___x_205_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__8));
v___x_206_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_204_);
lean_ctor_set(v___x_206_, 2, v___x_203_);
return v___x_206_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__5(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_207_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__4, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__4);
v___x_208_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__1, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__1);
v___x_209_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody___closed__0));
v___x_210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_208_);
lean_ctor_set(v___x_210_, 2, v___x_207_);
return v___x_210_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse(void){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__5, &lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse___closed__5);
return v___x_211_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_Sem(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_Lower(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_EmitCorrectRegion(uint8_t builtin) {
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
res = initialize_orb_x2dcompiler_Pancake_Lower(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk = _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_EmitCorrect_boundsChk);
lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody = _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody);
lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile = _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_EmitCorrect_scanWhile);
lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse = _init_lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_EmitCorrect_scanElse);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
