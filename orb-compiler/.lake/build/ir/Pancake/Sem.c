// Lean compiler output
// Module: Pancake.Sem
// Imports: public import Init public meta import Init
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
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_sub(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_not(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_BitVec_slt(lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_BitVec_setWidth(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* l_BitVec_repr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_BitVec_mul(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_byteAlign___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_byteAlign___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_byteAlign___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_byteAlign___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_byteAlign(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_byteAlign___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_byteIndex(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_byteIndex___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_getByte(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_getByte___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_wordSliceAlt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_wordSliceAlt___closed__0;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_wordSliceAlt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_wordSliceAlt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_setByte(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_setByte___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tag"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__1_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__4_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__3_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__6_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__7;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__8_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__10;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__11_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_instReprFinalEvent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprFinalEvent___closed__0_value;
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_instDecidableEqFinalEvent_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instDecidableEqFinalEvent_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_instDecidableEqFinalEvent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instDecidableEqFinalEvent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_error_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_error_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_timeout_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_timeout_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_break___00elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_break___00elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_continue___00elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_continue___00elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_return___00elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_return___00elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_finalFFI_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_finalFFI_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Pancake.Result.error"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Pancake.Result.timeout"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Pancake.Result.break_"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__4_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__5_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Pancake.Result.continue_"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__6_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__7_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Pancake.Result.return_"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__10_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__10_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__11_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__11_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__12_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Pancake.Result.finalFFI"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__13_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__13_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__14_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__14_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__15 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__15_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_instReprResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_instReprResult_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_instReprResult = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprResult___closed__0_value;
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_instDecidableEqResult_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instDecidableEqResult_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_instDecidableEqResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instDecidableEqResult___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_final_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_final_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ret_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ret_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memLoadByte(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memLoadByte___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memStoreWord___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memStoreWord___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memStoreWord(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memStoreByte___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memStoreByte___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memStoreByte(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memStoreByte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_readByteArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_readByteArray___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_readByteArray___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_readByteArray(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_readByteArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_writeByteArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_writeByteArray(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_add_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_add_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_add_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_add_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_and___00elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_and___00elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_and___00elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_and___00elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_sub_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_sub_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_sub_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_sub_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Pancake.Binop.add"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Pancake.Binop.and_"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Pancake.Binop.sub"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__4_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__5_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprBinop_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprBinop_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_instReprBinop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_instReprBinop_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprBinop___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprBinop___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_instReprBinop = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprBinop___closed__0_value;
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_Binop_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_instDecidableEqBinop(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instDecidableEqBinop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_less_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_less_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_less_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_less_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_equal_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_equal_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_equal_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_equal_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_notLess_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_notLess_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_notLess_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_notLess_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Pancake.Cmp.less"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Pancake.Cmp.equal"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Pancake.Cmp.notLess"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__4_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__5_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprCmp_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprCmp_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_instReprCmp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_instReprCmp_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprCmp___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprCmp___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_instReprCmp = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprCmp___closed__0_value;
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_Cmp_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_instDecidableEqCmp(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instDecidableEqCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_const_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_base_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_base_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_op_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_op_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_mul_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_mul_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_cmp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_cmp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_loadByte_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_loadByte_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_loadWord_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_loadWord_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Pancake.PancakeExp.base"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Pancake.PancakeExp.const"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__4_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Pancake.PancakeExp.var"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__7_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Pancake.PancakeExp.op"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__10_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Pancake.PancakeExp.mul"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__11_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__11_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__12_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__13_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Pancake.PancakeExp.cmp"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__14_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__14_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__15 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__15_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__16 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__16_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Pancake.PancakeExp.loadByte"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__17 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__17_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__17_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__18 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__18_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__18_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__19 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__19_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Pancake.PancakeExp.loadWord"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__20 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__20_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__20_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__21 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__21_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__21_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__22 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__22_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_instReprPancakeExp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeExp___closed__0_value;
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_signedLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_signedLt___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_eval___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_eval___redArg___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_eval___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_eval___redArg___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_eval___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_eval___redArg___closed__2;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__8_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__8_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_instReprBinop_repr_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_instReprBinop_repr_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_instReprBinop_repr_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_instReprBinop_repr_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__6_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__6_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_skip_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_skip_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_dec_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_dec_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_assign_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_assign_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_store_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_store_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_extCall_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_extCall_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_seq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_seq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_cond_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_cond_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_while___00elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_while___00elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_ret_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_ret_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_storeByte_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_storeByte_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Pancake.PancakeProg.skip"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Pancake.PancakeProg.dec"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__4_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Pancake.PancakeProg.assign"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__7_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Pancake.PancakeProg.store"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__10_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Pancake.PancakeProg.extCall"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__11_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__11_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__12_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__13_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Pancake.PancakeProg.seq"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__14_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__14_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__15 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__15_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__16 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__16_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Pancake.PancakeProg.cond"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__17 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__17_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__17_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__18 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__18_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__18_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__19 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__19_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Pancake.PancakeProg.while_"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__20 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__20_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__20_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__21 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__21_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__21_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__22 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__22_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Pancake.PancakeProg.ret"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__23 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__23_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__23_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__24 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__24_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__24_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__25 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__25_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Pancake.PancakeProg.storeByte"};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__26 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__26_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__26_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__27 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__27_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__27_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__28 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__28_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_instReprPancakeProg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg = (const lean_object*)&lp_orb_x2dcompiler_Pancake_instReprPancakeProg___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_setLocal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_setLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_resVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_resVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_emptyLocals___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_emptyLocals___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_emptyLocals___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_emptyLocals___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_emptyLocals___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_emptyLocals___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_emptyLocals___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_emptyLocals(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_decClock___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_decClock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_clampClock___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_clampClock(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeSem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeSem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__12_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__12_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_writeByteArray_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_writeByteArray_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__7_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__7_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__9_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__9_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_orb_x2dcompiler_Pancake_byteAlign___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_unsigned_to_nat(7u);
v___x_2_ = lean_unsigned_to_nat(64u);
v___x_3_ = l_BitVec_ofNat(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_byteAlign___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_byteAlign___closed__0, &lp_orb_x2dcompiler_Pancake_byteAlign___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_byteAlign___closed__0);
v___x_5_ = lean_unsigned_to_nat(64u);
v___x_6_ = l_BitVec_not(v___x_5_, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_byteAlign(lean_object* v_w_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_byteAlign___closed__1, &lp_orb_x2dcompiler_Pancake_byteAlign___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_byteAlign___closed__1);
v___x_9_ = lean_nat_land(v_w_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_byteAlign___boxed(lean_object* v_w_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_orb_x2dcompiler_Pancake_byteAlign(v_w_10_);
lean_dec(v_w_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_byteIndex(lean_object* v_a_12_, uint8_t v_be_13_){
_start:
{
lean_object* v_d_14_; 
v_d_14_ = lean_unsigned_to_nat(8u);
if (v_be_13_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_nat_mod(v_a_12_, v_d_14_);
v___x_16_ = lean_nat_mul(v_d_14_, v___x_15_);
lean_dec(v___x_15_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_17_ = lean_unsigned_to_nat(7u);
v___x_18_ = lean_nat_mod(v_a_12_, v_d_14_);
v___x_19_ = lean_nat_sub(v___x_17_, v___x_18_);
lean_dec(v___x_18_);
v___x_20_ = lean_nat_mul(v_d_14_, v___x_19_);
lean_dec(v___x_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_byteIndex___boxed(lean_object* v_a_21_, lean_object* v_be_22_){
_start:
{
uint8_t v_be_boxed_23_; lean_object* v_res_24_; 
v_be_boxed_23_ = lean_unbox(v_be_22_);
v_res_24_ = lp_orb_x2dcompiler_Pancake_byteIndex(v_a_21_, v_be_boxed_23_);
lean_dec(v_a_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_getByte(lean_object* v_a_25_, lean_object* v_w_26_, uint8_t v_be_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_28_ = lean_unsigned_to_nat(64u);
v___x_29_ = lean_unsigned_to_nat(8u);
v___x_30_ = lp_orb_x2dcompiler_Pancake_byteIndex(v_a_25_, v_be_27_);
v___x_31_ = lean_nat_shiftr(v_w_26_, v___x_30_);
lean_dec(v___x_30_);
v___x_32_ = l_BitVec_setWidth(v___x_28_, v___x_29_, v___x_31_);
lean_dec(v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_getByte___boxed(lean_object* v_a_33_, lean_object* v_w_34_, lean_object* v_be_35_){
_start:
{
uint8_t v_be_boxed_36_; lean_object* v_res_37_; 
v_be_boxed_36_ = lean_unbox(v_be_35_);
v_res_37_ = lp_orb_x2dcompiler_Pancake_getByte(v_a_33_, v_w_34_, v_be_boxed_36_);
lean_dec(v_w_34_);
lean_dec(v_a_33_);
return v_res_37_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_wordSliceAlt___closed__0(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_unsigned_to_nat(1u);
v___x_39_ = lean_unsigned_to_nat(64u);
v___x_40_ = l_BitVec_ofNat(v___x_39_, v___x_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_wordSliceAlt(lean_object* v_hi_41_, lean_object* v_lo_42_, lean_object* v_w_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v_low_47_; lean_object* v___x_48_; lean_object* v_high_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_44_ = lean_unsigned_to_nat(64u);
v___x_45_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_wordSliceAlt___closed__0, &lp_orb_x2dcompiler_Pancake_wordSliceAlt___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_wordSliceAlt___closed__0);
v___x_46_ = l_BitVec_shiftLeft(v___x_44_, v___x_45_, v_lo_42_);
v_low_47_ = l_BitVec_sub(v___x_44_, v___x_46_, v___x_45_);
lean_dec(v___x_46_);
v___x_48_ = l_BitVec_shiftLeft(v___x_44_, v___x_45_, v_hi_41_);
v_high_49_ = l_BitVec_sub(v___x_44_, v___x_48_, v___x_45_);
lean_dec(v___x_48_);
v___x_50_ = l_BitVec_not(v___x_44_, v_low_47_);
lean_dec(v_low_47_);
v___x_51_ = lean_nat_land(v_high_49_, v___x_50_);
lean_dec(v___x_50_);
lean_dec(v_high_49_);
v___x_52_ = lean_nat_land(v_w_43_, v___x_51_);
lean_dec(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_wordSliceAlt___boxed(lean_object* v_hi_53_, lean_object* v_lo_54_, lean_object* v_w_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lp_orb_x2dcompiler_Pancake_wordSliceAlt(v_hi_53_, v_lo_54_, v_w_55_);
lean_dec(v_w_55_);
lean_dec(v_lo_54_);
lean_dec(v_hi_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_setByte(lean_object* v_a_57_, lean_object* v_b_58_, lean_object* v_w_59_, uint8_t v_be_60_){
_start:
{
lean_object* v_i_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_i_61_ = lp_orb_x2dcompiler_Pancake_byteIndex(v_a_57_, v_be_60_);
v___x_62_ = lean_unsigned_to_nat(64u);
v___x_63_ = lean_unsigned_to_nat(8u);
v___x_64_ = lean_nat_add(v_i_61_, v___x_63_);
v___x_65_ = lp_orb_x2dcompiler_Pancake_wordSliceAlt(v___x_62_, v___x_64_, v_w_59_);
lean_dec(v___x_64_);
v___x_66_ = l_BitVec_setWidth(v___x_63_, v___x_62_, v_b_58_);
v___x_67_ = l_BitVec_shiftLeft(v___x_62_, v___x_66_, v_i_61_);
lean_dec(v___x_66_);
v___x_68_ = lean_nat_lor(v___x_65_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v___x_65_);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lp_orb_x2dcompiler_Pancake_wordSliceAlt(v_i_61_, v___x_69_, v_w_59_);
lean_dec(v_i_61_);
v___x_71_ = lean_nat_lor(v___x_68_, v___x_70_);
lean_dec(v___x_70_);
lean_dec(v___x_68_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_setByte___boxed(lean_object* v_a_72_, lean_object* v_b_73_, lean_object* v_w_74_, lean_object* v_be_75_){
_start:
{
uint8_t v_be_boxed_76_; lean_object* v_res_77_; 
v_be_boxed_76_ = lean_unbox(v_be_75_);
v_res_77_ = lp_orb_x2dcompiler_Pancake_setByte(v_a_72_, v_b_73_, v_w_74_, v_be_boxed_76_);
lean_dec(v_w_74_);
lean_dec(v_b_73_);
lean_dec(v_a_72_);
return v_res_77_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_unsigned_to_nat(7u);
v___x_92_ = lean_nat_to_int(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__0));
v___x_95_ = lean_string_length(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__9, &lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__9);
v___x_97_ = lean_nat_to_int(v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg(lean_object* v_x_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_103_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__6));
v___x_104_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__7, &lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__7);
v___x_105_ = l_String_quote(v_x_102_);
v___x_106_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
v___x_107_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_104_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = 0;
v___x_109_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_109_, 0, v___x_107_);
lean_ctor_set_uint8(v___x_109_, sizeof(void*)*1, v___x_108_);
v___x_110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_103_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__10, &lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__10);
v___x_112_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__11));
v___x_113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___x_110_);
v___x_114_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg___closed__12));
v___x_115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_111_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_108_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr(lean_object* v_x_118_, lean_object* v_prec_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg(v_x_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___boxed(lean_object* v_x_121_, lean_object* v_prec_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr(v_x_121_, v_prec_122_);
lean_dec(v_prec_122_);
return v_res_123_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_instDecidableEqFinalEvent_decEq(lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
uint8_t v___x_128_; 
v___x_128_ = lean_string_dec_eq(v_x_126_, v_x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instDecidableEqFinalEvent_decEq___boxed(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = lp_orb_x2dcompiler_Pancake_instDecidableEqFinalEvent_decEq(v_x_129_, v_x_130_);
lean_dec_ref(v_x_130_);
lean_dec_ref(v_x_129_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_instDecidableEqFinalEvent(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
uint8_t v___x_135_; 
v___x_135_ = lean_string_dec_eq(v_x_133_, v_x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instDecidableEqFinalEvent___boxed(lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = lp_orb_x2dcompiler_Pancake_instDecidableEqFinalEvent(v_x_136_, v_x_137_);
lean_dec_ref(v_x_137_);
lean_dec_ref(v_x_136_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_ctorIdx(lean_object* v_x_140_){
_start:
{
switch(lean_obj_tag(v_x_140_))
{
case 0:
{
lean_object* v___x_141_; 
v___x_141_ = lean_unsigned_to_nat(0u);
return v___x_141_;
}
case 1:
{
lean_object* v___x_142_; 
v___x_142_ = lean_unsigned_to_nat(1u);
return v___x_142_;
}
case 2:
{
lean_object* v___x_143_; 
v___x_143_ = lean_unsigned_to_nat(2u);
return v___x_143_;
}
case 3:
{
lean_object* v___x_144_; 
v___x_144_ = lean_unsigned_to_nat(3u);
return v___x_144_;
}
case 4:
{
lean_object* v___x_145_; 
v___x_145_ = lean_unsigned_to_nat(4u);
return v___x_145_;
}
default: 
{
lean_object* v___x_146_; 
v___x_146_ = lean_unsigned_to_nat(5u);
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_ctorIdx___boxed(lean_object* v_x_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = lp_orb_x2dcompiler_Pancake_Result_ctorIdx(v_x_147_);
lean_dec(v_x_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_ctorElim___redArg(lean_object* v_t_149_, lean_object* v_k_150_){
_start:
{
switch(lean_obj_tag(v_t_149_))
{
case 4:
{
lean_object* v_v_151_; lean_object* v___x_152_; 
v_v_151_ = lean_ctor_get(v_t_149_, 0);
lean_inc(v_v_151_);
lean_dec_ref(v_t_149_);
v___x_152_ = lean_apply_1(v_k_150_, v_v_151_);
return v___x_152_;
}
case 5:
{
lean_object* v_outcome_153_; lean_object* v___x_154_; 
v_outcome_153_ = lean_ctor_get(v_t_149_, 0);
lean_inc_ref(v_outcome_153_);
lean_dec_ref(v_t_149_);
v___x_154_ = lean_apply_1(v_k_150_, v_outcome_153_);
return v___x_154_;
}
default: 
{
lean_dec(v_t_149_);
return v_k_150_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_ctorElim(lean_object* v_motive_155_, lean_object* v_ctorIdx_156_, lean_object* v_t_157_, lean_object* v_h_158_, lean_object* v_k_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lp_orb_x2dcompiler_Pancake_Result_ctorElim___redArg(v_t_157_, v_k_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_ctorElim___boxed(lean_object* v_motive_161_, lean_object* v_ctorIdx_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_k_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = lp_orb_x2dcompiler_Pancake_Result_ctorElim(v_motive_161_, v_ctorIdx_162_, v_t_163_, v_h_164_, v_k_165_);
lean_dec(v_ctorIdx_162_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_error_elim___redArg(lean_object* v_t_167_, lean_object* v_error_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lp_orb_x2dcompiler_Pancake_Result_ctorElim___redArg(v_t_167_, v_error_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_error_elim(lean_object* v_motive_170_, lean_object* v_t_171_, lean_object* v_h_172_, lean_object* v_error_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lp_orb_x2dcompiler_Pancake_Result_ctorElim___redArg(v_t_171_, v_error_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_timeout_elim___redArg(lean_object* v_t_175_, lean_object* v_timeout_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lp_orb_x2dcompiler_Pancake_Result_ctorElim___redArg(v_t_175_, v_timeout_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_timeout_elim(lean_object* v_motive_178_, lean_object* v_t_179_, lean_object* v_h_180_, lean_object* v_timeout_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lp_orb_x2dcompiler_Pancake_Result_ctorElim___redArg(v_t_179_, v_timeout_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_break___00elim___redArg(lean_object* v_t_183_, lean_object* v_break___184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lp_orb_x2dcompiler_Pancake_Result_ctorElim___redArg(v_t_183_, v_break___184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_break___00elim(lean_object* v_motive_186_, lean_object* v_t_187_, lean_object* v_h_188_, lean_object* v_break___189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lp_orb_x2dcompiler_Pancake_Result_ctorElim___redArg(v_t_187_, v_break___189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_continue___00elim___redArg(lean_object* v_t_191_, lean_object* v_continue___192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lp_orb_x2dcompiler_Pancake_Result_ctorElim___redArg(v_t_191_, v_continue___192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_continue___00elim(lean_object* v_motive_194_, lean_object* v_t_195_, lean_object* v_h_196_, lean_object* v_continue___197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lp_orb_x2dcompiler_Pancake_Result_ctorElim___redArg(v_t_195_, v_continue___197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_return___00elim___redArg(lean_object* v_t_199_, lean_object* v_return___200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lp_orb_x2dcompiler_Pancake_Result_ctorElim___redArg(v_t_199_, v_return___200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_return___00elim(lean_object* v_motive_202_, lean_object* v_t_203_, lean_object* v_h_204_, lean_object* v_return___205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lp_orb_x2dcompiler_Pancake_Result_ctorElim___redArg(v_t_203_, v_return___205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_finalFFI_elim___redArg(lean_object* v_t_207_, lean_object* v_finalFFI_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lp_orb_x2dcompiler_Pancake_Result_ctorElim___redArg(v_t_207_, v_finalFFI_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Result_finalFFI_elim(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_finalFFI_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lp_orb_x2dcompiler_Pancake_Result_ctorElim___redArg(v_t_211_, v_finalFFI_213_);
return v___x_214_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_unsigned_to_nat(2u);
v___x_228_ = lean_nat_to_int(v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_unsigned_to_nat(1u);
v___x_230_ = lean_nat_to_int(v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr(lean_object* v_x_243_, lean_object* v_prec_244_){
_start:
{
lean_object* v___y_246_; lean_object* v___y_253_; lean_object* v___y_260_; lean_object* v___y_267_; 
switch(lean_obj_tag(v_x_243_))
{
case 0:
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(1024u);
v___x_274_ = lean_nat_dec_le(v___x_273_, v_prec_244_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
v___x_275_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_246_ = v___x_275_;
goto v___jp_245_;
}
else
{
lean_object* v___x_276_; 
v___x_276_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_246_ = v___x_276_;
goto v___jp_245_;
}
}
case 1:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(1024u);
v___x_278_ = lean_nat_dec_le(v___x_277_, v_prec_244_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
v___x_279_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_253_ = v___x_279_;
goto v___jp_252_;
}
else
{
lean_object* v___x_280_; 
v___x_280_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_253_ = v___x_280_;
goto v___jp_252_;
}
}
case 2:
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(1024u);
v___x_282_ = lean_nat_dec_le(v___x_281_, v_prec_244_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; 
v___x_283_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_260_ = v___x_283_;
goto v___jp_259_;
}
else
{
lean_object* v___x_284_; 
v___x_284_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_260_ = v___x_284_;
goto v___jp_259_;
}
}
case 3:
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(1024u);
v___x_286_ = lean_nat_dec_le(v___x_285_, v_prec_244_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; 
v___x_287_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_267_ = v___x_287_;
goto v___jp_266_;
}
else
{
lean_object* v___x_288_; 
v___x_288_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_267_ = v___x_288_;
goto v___jp_266_;
}
}
case 4:
{
lean_object* v_v_289_; lean_object* v___y_291_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_v_289_ = lean_ctor_get(v_x_243_, 0);
lean_inc(v_v_289_);
lean_dec_ref(v_x_243_);
v___x_300_ = lean_unsigned_to_nat(1024u);
v___x_301_ = lean_nat_dec_le(v___x_300_, v_prec_244_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_291_ = v___x_302_;
goto v___jp_290_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_291_ = v___x_303_;
goto v___jp_290_;
}
v___jp_290_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_292_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__12));
v___x_293_ = lean_unsigned_to_nat(64u);
v___x_294_ = l_BitVec_repr(v___x_293_, v_v_289_);
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_292_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
lean_inc(v___y_291_);
v___x_296_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_296_, 0, v___y_291_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = 0;
v___x_298_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set_uint8(v___x_298_, sizeof(void*)*1, v___x_297_);
v___x_299_ = l_Repr_addAppParen(v___x_298_, v_prec_244_);
return v___x_299_;
}
}
default: 
{
lean_object* v_outcome_304_; lean_object* v___y_306_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_outcome_304_ = lean_ctor_get(v_x_243_, 0);
lean_inc_ref(v_outcome_304_);
lean_dec_ref(v_x_243_);
v___x_314_ = lean_unsigned_to_nat(1024u);
v___x_315_ = lean_nat_dec_le(v___x_314_, v_prec_244_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
v___x_316_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_306_ = v___x_316_;
goto v___jp_305_;
}
else
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_306_ = v___x_317_;
goto v___jp_305_;
}
v___jp_305_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_307_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__15));
v___x_308_ = lp_orb_x2dcompiler_Pancake_instReprFinalEvent_repr___redArg(v_outcome_304_);
v___x_309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
lean_inc(v___y_306_);
v___x_310_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_310_, 0, v___y_306_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = 0;
v___x_312_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set_uint8(v___x_312_, sizeof(void*)*1, v___x_311_);
v___x_313_ = l_Repr_addAppParen(v___x_312_, v_prec_244_);
return v___x_313_;
}
}
}
v___jp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_247_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__1));
lean_inc(v___y_246_);
v___x_248_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_248_, 0, v___y_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = 0;
v___x_250_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*1, v___x_249_);
v___x_251_ = l_Repr_addAppParen(v___x_250_, v_prec_244_);
return v___x_251_;
}
v___jp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_254_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__3));
lean_inc(v___y_253_);
v___x_255_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_255_, 0, v___y_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = 0;
v___x_257_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*1, v___x_256_);
v___x_258_ = l_Repr_addAppParen(v___x_257_, v_prec_244_);
return v___x_258_;
}
v___jp_259_:
{
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_261_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__5));
lean_inc(v___y_260_);
v___x_262_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_262_, 0, v___y_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = 0;
v___x_264_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set_uint8(v___x_264_, sizeof(void*)*1, v___x_263_);
v___x_265_ = l_Repr_addAppParen(v___x_264_, v_prec_244_);
return v___x_265_;
}
v___jp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_268_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__7));
lean_inc(v___y_267_);
v___x_269_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_269_, 0, v___y_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = 0;
v___x_271_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*1, v___x_270_);
v___x_272_ = l_Repr_addAppParen(v___x_271_, v_prec_244_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprResult_repr___boxed(lean_object* v_x_318_, lean_object* v_prec_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = lp_orb_x2dcompiler_Pancake_instReprResult_repr(v_x_318_, v_prec_319_);
lean_dec(v_prec_319_);
return v_res_320_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_instDecidableEqResult_decEq(lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
switch(lean_obj_tag(v_x_323_))
{
case 0:
{
switch(lean_obj_tag(v_x_324_))
{
case 0:
{
uint8_t v___x_325_; 
v___x_325_ = 1;
return v___x_325_;
}
case 4:
{
uint8_t v___x_326_; 
v___x_326_ = 0;
return v___x_326_;
}
case 5:
{
uint8_t v___x_327_; 
v___x_327_ = 0;
return v___x_327_;
}
default: 
{
uint8_t v___x_328_; 
v___x_328_ = 0;
return v___x_328_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_x_324_))
{
case 1:
{
uint8_t v___x_329_; 
v___x_329_ = 1;
return v___x_329_;
}
case 4:
{
uint8_t v___x_330_; 
v___x_330_ = 0;
return v___x_330_;
}
case 5:
{
uint8_t v___x_331_; 
v___x_331_ = 0;
return v___x_331_;
}
default: 
{
uint8_t v___x_332_; 
v___x_332_ = 0;
return v___x_332_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_x_324_))
{
case 2:
{
uint8_t v___x_333_; 
v___x_333_ = 1;
return v___x_333_;
}
case 4:
{
uint8_t v___x_334_; 
v___x_334_ = 0;
return v___x_334_;
}
case 5:
{
uint8_t v___x_335_; 
v___x_335_ = 0;
return v___x_335_;
}
default: 
{
uint8_t v___x_336_; 
v___x_336_ = 0;
return v___x_336_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_324_))
{
case 3:
{
uint8_t v___x_337_; 
v___x_337_ = 1;
return v___x_337_;
}
case 4:
{
uint8_t v___x_338_; 
v___x_338_ = 0;
return v___x_338_;
}
case 5:
{
uint8_t v___x_339_; 
v___x_339_ = 0;
return v___x_339_;
}
default: 
{
uint8_t v___x_340_; 
v___x_340_ = 0;
return v___x_340_;
}
}
}
case 4:
{
lean_object* v_v_341_; uint8_t v___x_342_; 
v_v_341_ = lean_ctor_get(v_x_323_, 0);
v___x_342_ = 0;
if (lean_obj_tag(v_x_324_) == 4)
{
lean_object* v_v_343_; uint8_t v___x_344_; 
v_v_343_ = lean_ctor_get(v_x_324_, 0);
v___x_344_ = lean_nat_dec_eq(v_v_341_, v_v_343_);
if (v___x_344_ == 0)
{
return v___x_342_;
}
else
{
return v___x_344_;
}
}
else
{
return v___x_342_;
}
}
default: 
{
lean_object* v_outcome_345_; uint8_t v___x_346_; 
v_outcome_345_ = lean_ctor_get(v_x_323_, 0);
v___x_346_ = 0;
if (lean_obj_tag(v_x_324_) == 5)
{
lean_object* v_outcome_347_; uint8_t v___x_348_; 
v_outcome_347_ = lean_ctor_get(v_x_324_, 0);
v___x_348_ = lean_string_dec_eq(v_outcome_345_, v_outcome_347_);
if (v___x_348_ == 0)
{
return v___x_346_;
}
else
{
return v___x_348_;
}
}
else
{
return v___x_346_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instDecidableEqResult_decEq___boxed(lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = lp_orb_x2dcompiler_Pancake_instDecidableEqResult_decEq(v_x_349_, v_x_350_);
lean_dec(v_x_350_);
lean_dec(v_x_349_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_instDecidableEqResult(lean_object* v_x_353_, lean_object* v_x_354_){
_start:
{
uint8_t v___x_355_; 
v___x_355_ = lp_orb_x2dcompiler_Pancake_instDecidableEqResult_decEq(v_x_353_, v_x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instDecidableEqResult___boxed(lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = lp_orb_x2dcompiler_Pancake_instDecidableEqResult(v_x_356_, v_x_357_);
lean_dec(v_x_357_);
lean_dec(v_x_356_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ctorIdx___redArg(lean_object* v_x_360_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
lean_object* v___x_361_; 
v___x_361_ = lean_unsigned_to_nat(0u);
return v___x_361_;
}
else
{
lean_object* v___x_362_; 
v___x_362_ = lean_unsigned_to_nat(1u);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ctorIdx___redArg___boxed(lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = lp_orb_x2dcompiler_Pancake_FFIResult_ctorIdx___redArg(v_x_363_);
lean_dec_ref(v_x_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ctorIdx(lean_object* v_00_u03c3_365_, lean_object* v_x_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lp_orb_x2dcompiler_Pancake_FFIResult_ctorIdx___redArg(v_x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ctorIdx___boxed(lean_object* v_00_u03c3_368_, lean_object* v_x_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = lp_orb_x2dcompiler_Pancake_FFIResult_ctorIdx(v_00_u03c3_368_, v_x_369_);
lean_dec_ref(v_x_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ctorElim___redArg(lean_object* v_t_371_, lean_object* v_k_372_){
_start:
{
if (lean_obj_tag(v_t_371_) == 0)
{
lean_object* v_outcome_373_; lean_object* v___x_374_; 
v_outcome_373_ = lean_ctor_get(v_t_371_, 0);
lean_inc_ref(v_outcome_373_);
lean_dec_ref(v_t_371_);
v___x_374_ = lean_apply_1(v_k_372_, v_outcome_373_);
return v___x_374_;
}
else
{
lean_object* v_newState_375_; lean_object* v_newBytes_376_; lean_object* v___x_377_; 
v_newState_375_ = lean_ctor_get(v_t_371_, 0);
lean_inc(v_newState_375_);
v_newBytes_376_ = lean_ctor_get(v_t_371_, 1);
lean_inc(v_newBytes_376_);
lean_dec_ref(v_t_371_);
v___x_377_ = lean_apply_2(v_k_372_, v_newState_375_, v_newBytes_376_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ctorElim(lean_object* v_00_u03c3_378_, lean_object* v_motive_379_, lean_object* v_ctorIdx_380_, lean_object* v_t_381_, lean_object* v_h_382_, lean_object* v_k_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = lp_orb_x2dcompiler_Pancake_FFIResult_ctorElim___redArg(v_t_381_, v_k_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ctorElim___boxed(lean_object* v_00_u03c3_385_, lean_object* v_motive_386_, lean_object* v_ctorIdx_387_, lean_object* v_t_388_, lean_object* v_h_389_, lean_object* v_k_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = lp_orb_x2dcompiler_Pancake_FFIResult_ctorElim(v_00_u03c3_385_, v_motive_386_, v_ctorIdx_387_, v_t_388_, v_h_389_, v_k_390_);
lean_dec(v_ctorIdx_387_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_final_elim___redArg(lean_object* v_t_392_, lean_object* v_final_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = lp_orb_x2dcompiler_Pancake_FFIResult_ctorElim___redArg(v_t_392_, v_final_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_final_elim(lean_object* v_00_u03c3_395_, lean_object* v_motive_396_, lean_object* v_t_397_, lean_object* v_h_398_, lean_object* v_final_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lp_orb_x2dcompiler_Pancake_FFIResult_ctorElim___redArg(v_t_397_, v_final_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ret_elim___redArg(lean_object* v_t_401_, lean_object* v_ret_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = lp_orb_x2dcompiler_Pancake_FFIResult_ctorElim___redArg(v_t_401_, v_ret_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FFIResult_ret_elim(lean_object* v_00_u03c3_404_, lean_object* v_motive_405_, lean_object* v_t_406_, lean_object* v_h_407_, lean_object* v_ret_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = lp_orb_x2dcompiler_Pancake_FFIResult_ctorElim___redArg(v_t_406_, v_ret_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memLoadByte(lean_object* v_m_410_, lean_object* v_dm_411_, uint8_t v_be_412_, lean_object* v_w_413_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_414_ = lp_orb_x2dcompiler_Pancake_byteAlign(v_w_413_);
lean_inc(v___x_414_);
v___x_415_ = lean_apply_1(v_dm_411_, v___x_414_);
v___x_416_ = lean_unbox(v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; 
lean_dec(v___x_414_);
lean_dec_ref(v_m_410_);
v___x_417_ = lean_box(0);
return v___x_417_;
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = lean_apply_1(v_m_410_, v___x_414_);
v___x_419_ = lp_orb_x2dcompiler_Pancake_getByte(v_w_413_, v___x_418_, v_be_412_);
lean_dec(v___x_418_);
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memLoadByte___boxed(lean_object* v_m_421_, lean_object* v_dm_422_, lean_object* v_be_423_, lean_object* v_w_424_){
_start:
{
uint8_t v_be_boxed_425_; lean_object* v_res_426_; 
v_be_boxed_425_ = lean_unbox(v_be_423_);
v_res_426_ = lp_orb_x2dcompiler_Pancake_memLoadByte(v_m_421_, v_dm_422_, v_be_boxed_425_, v_w_424_);
lean_dec(v_w_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memStoreWord___lam__0(lean_object* v_addr_427_, lean_object* v_m_428_, lean_object* v_w_429_, lean_object* v_k_430_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = lean_nat_dec_eq(v_k_430_, v_addr_427_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
v___x_432_ = lean_apply_1(v_m_428_, v_k_430_);
return v___x_432_;
}
else
{
lean_dec(v_k_430_);
lean_dec_ref(v_m_428_);
lean_inc(v_w_429_);
return v_w_429_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memStoreWord___lam__0___boxed(lean_object* v_addr_433_, lean_object* v_m_434_, lean_object* v_w_435_, lean_object* v_k_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = lp_orb_x2dcompiler_Pancake_memStoreWord___lam__0(v_addr_433_, v_m_434_, v_w_435_, v_k_436_);
lean_dec(v_w_435_);
lean_dec(v_addr_433_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memStoreWord(lean_object* v_m_438_, lean_object* v_dm_439_, lean_object* v_addr_440_, lean_object* v_w_441_){
_start:
{
lean_object* v___x_442_; uint8_t v___x_443_; 
lean_inc(v_addr_440_);
v___x_442_ = lean_apply_1(v_dm_439_, v_addr_440_);
v___x_443_ = lean_unbox(v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
lean_dec(v_w_441_);
lean_dec(v_addr_440_);
lean_dec_ref(v_m_438_);
v___x_444_ = lean_box(0);
return v___x_444_;
}
else
{
lean_object* v___f_445_; lean_object* v___x_446_; 
v___f_445_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_memStoreWord___lam__0___boxed), 4, 3);
lean_closure_set(v___f_445_, 0, v_addr_440_);
lean_closure_set(v___f_445_, 1, v_m_438_);
lean_closure_set(v___f_445_, 2, v_w_441_);
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v___f_445_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memStoreByte___lam__0(lean_object* v___x_447_, lean_object* v_m_448_, lean_object* v_w_449_, lean_object* v_b_450_, uint8_t v_be_451_, lean_object* v_k_452_){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = lean_nat_dec_eq(v_k_452_, v___x_447_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
lean_dec(v___x_447_);
v___x_454_ = lean_apply_1(v_m_448_, v_k_452_);
return v___x_454_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec(v_k_452_);
v___x_455_ = lean_apply_1(v_m_448_, v___x_447_);
v___x_456_ = lp_orb_x2dcompiler_Pancake_setByte(v_w_449_, v_b_450_, v___x_455_, v_be_451_);
lean_dec(v___x_455_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memStoreByte___lam__0___boxed(lean_object* v___x_457_, lean_object* v_m_458_, lean_object* v_w_459_, lean_object* v_b_460_, lean_object* v_be_461_, lean_object* v_k_462_){
_start:
{
uint8_t v_be_boxed_463_; lean_object* v_res_464_; 
v_be_boxed_463_ = lean_unbox(v_be_461_);
v_res_464_ = lp_orb_x2dcompiler_Pancake_memStoreByte___lam__0(v___x_457_, v_m_458_, v_w_459_, v_b_460_, v_be_boxed_463_, v_k_462_);
lean_dec(v_b_460_);
lean_dec(v_w_459_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memStoreByte(lean_object* v_m_465_, lean_object* v_dm_466_, uint8_t v_be_467_, lean_object* v_w_468_, lean_object* v_b_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_470_ = lp_orb_x2dcompiler_Pancake_byteAlign(v_w_468_);
lean_inc(v___x_470_);
v___x_471_ = lean_apply_1(v_dm_466_, v___x_470_);
v___x_472_ = lean_unbox(v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; 
lean_dec(v___x_470_);
lean_dec(v_b_469_);
lean_dec(v_w_468_);
lean_dec_ref(v_m_465_);
v___x_473_ = lean_box(0);
return v___x_473_;
}
else
{
lean_object* v___x_474_; lean_object* v___f_475_; lean_object* v___x_476_; 
v___x_474_ = lean_box(v_be_467_);
v___f_475_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_memStoreByte___lam__0___boxed), 6, 5);
lean_closure_set(v___f_475_, 0, v___x_470_);
lean_closure_set(v___f_475_, 1, v_m_465_);
lean_closure_set(v___f_475_, 2, v_w_468_);
lean_closure_set(v___f_475_, 3, v_b_469_);
lean_closure_set(v___f_475_, 4, v___x_474_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v___f_475_);
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_memStoreByte___boxed(lean_object* v_m_477_, lean_object* v_dm_478_, lean_object* v_be_479_, lean_object* v_w_480_, lean_object* v_b_481_){
_start:
{
uint8_t v_be_boxed_482_; lean_object* v_res_483_; 
v_be_boxed_482_ = lean_unbox(v_be_479_);
v_res_483_ = lp_orb_x2dcompiler_Pancake_memStoreByte(v_m_477_, v_dm_478_, v_be_boxed_482_, v_w_480_, v_b_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_readByteArray(lean_object* v_m_486_, lean_object* v_dm_487_, uint8_t v_be_488_, lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
lean_object* v_zero_491_; uint8_t v_isZero_492_; 
v_zero_491_ = lean_unsigned_to_nat(0u);
v_isZero_492_ = lean_nat_dec_eq(v_x_490_, v_zero_491_);
if (v_isZero_492_ == 1)
{
lean_object* v___x_493_; 
lean_dec_ref(v_dm_487_);
lean_dec_ref(v_m_486_);
v___x_493_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_readByteArray___closed__0));
return v___x_493_;
}
else
{
lean_object* v___x_494_; 
lean_inc_ref(v_dm_487_);
lean_inc_ref(v_m_486_);
v___x_494_ = lp_orb_x2dcompiler_Pancake_memLoadByte(v_m_486_, v_dm_487_, v_be_488_, v_x_489_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v___x_495_; 
lean_dec_ref(v_dm_487_);
lean_dec_ref(v_m_486_);
v___x_495_ = lean_box(0);
return v___x_495_;
}
else
{
lean_object* v_val_496_; lean_object* v_one_497_; lean_object* v_n_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_val_496_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_val_496_);
lean_dec_ref(v___x_494_);
v_one_497_ = lean_unsigned_to_nat(1u);
v_n_498_ = lean_nat_sub(v_x_490_, v_one_497_);
v___x_499_ = lean_unsigned_to_nat(64u);
v___x_500_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_wordSliceAlt___closed__0, &lp_orb_x2dcompiler_Pancake_wordSliceAlt___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_wordSliceAlt___closed__0);
v___x_501_ = l_BitVec_add(v___x_499_, v_x_489_, v___x_500_);
v___x_502_ = lp_orb_x2dcompiler_Pancake_readByteArray(v_m_486_, v_dm_487_, v_be_488_, v___x_501_, v_n_498_);
lean_dec(v_n_498_);
lean_dec(v___x_501_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_dec(v_val_496_);
return v___x_502_;
}
else
{
lean_object* v_val_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_511_; 
v_val_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_511_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_val_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_507_, 0, v_val_496_);
lean_ctor_set(v___x_507_, 1, v_val_503_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_507_);
v___x_509_ = v___x_505_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_readByteArray___boxed(lean_object* v_m_512_, lean_object* v_dm_513_, lean_object* v_be_514_, lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
uint8_t v_be_boxed_517_; lean_object* v_res_518_; 
v_be_boxed_517_ = lean_unbox(v_be_514_);
v_res_518_ = lp_orb_x2dcompiler_Pancake_readByteArray(v_m_512_, v_dm_513_, v_be_boxed_517_, v_x_515_, v_x_516_);
lean_dec(v_x_516_);
lean_dec(v_x_515_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_writeByteArray___boxed(lean_object* v_dm_519_, lean_object* v_be_520_, lean_object* v_x_521_, lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v_a_524_){
_start:
{
uint8_t v_be_boxed_525_; lean_object* v_res_526_; 
v_be_boxed_525_ = lean_unbox(v_be_520_);
v_res_526_ = lp_orb_x2dcompiler_Pancake_writeByteArray(v_dm_519_, v_be_boxed_525_, v_x_521_, v_x_522_, v_x_523_, v_a_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_writeByteArray(lean_object* v_dm_527_, uint8_t v_be_528_, lean_object* v_x_529_, lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v_a_532_){
_start:
{
if (lean_obj_tag(v_x_530_) == 0)
{
lean_object* v___x_533_; 
lean_dec(v_x_529_);
lean_dec_ref(v_dm_527_);
v___x_533_ = lean_apply_1(v_x_531_, v_a_532_);
return v___x_533_;
}
else
{
lean_object* v_head_534_; lean_object* v_tail_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_m_x27_540_; lean_object* v___x_541_; 
v_head_534_ = lean_ctor_get(v_x_530_, 0);
lean_inc(v_head_534_);
v_tail_535_ = lean_ctor_get(v_x_530_, 1);
lean_inc_n(v_tail_535_, 2);
lean_dec_ref(v_x_530_);
v___x_536_ = lean_unsigned_to_nat(64u);
v___x_537_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_wordSliceAlt___closed__0, &lp_orb_x2dcompiler_Pancake_wordSliceAlt___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_wordSliceAlt___closed__0);
v___x_538_ = l_BitVec_add(v___x_536_, v_x_529_, v___x_537_);
v___x_539_ = lean_box(v_be_528_);
lean_inc_ref(v_x_531_);
lean_inc(v___x_538_);
lean_inc_ref_n(v_dm_527_, 2);
v_m_x27_540_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_writeByteArray___boxed), 6, 5);
lean_closure_set(v_m_x27_540_, 0, v_dm_527_);
lean_closure_set(v_m_x27_540_, 1, v___x_539_);
lean_closure_set(v_m_x27_540_, 2, v___x_538_);
lean_closure_set(v_m_x27_540_, 3, v_tail_535_);
lean_closure_set(v_m_x27_540_, 4, v_x_531_);
v___x_541_ = lp_orb_x2dcompiler_Pancake_memStoreByte(v_m_x27_540_, v_dm_527_, v_be_528_, v_x_529_, v_head_534_);
if (lean_obj_tag(v___x_541_) == 0)
{
v_x_529_ = v___x_538_;
v_x_530_ = v_tail_535_;
goto _start;
}
else
{
lean_object* v_val_543_; lean_object* v___x_544_; 
lean_dec(v___x_538_);
lean_dec(v_tail_535_);
lean_dec_ref(v_x_531_);
lean_dec_ref(v_dm_527_);
v_val_543_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_val_543_);
lean_dec_ref(v___x_541_);
v___x_544_ = lean_apply_1(v_val_543_, v_a_532_);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_ctorIdx(uint8_t v_x_545_){
_start:
{
switch(v_x_545_)
{
case 0:
{
lean_object* v___x_546_; 
v___x_546_ = lean_unsigned_to_nat(0u);
return v___x_546_;
}
case 1:
{
lean_object* v___x_547_; 
v___x_547_ = lean_unsigned_to_nat(1u);
return v___x_547_;
}
default: 
{
lean_object* v___x_548_; 
v___x_548_ = lean_unsigned_to_nat(2u);
return v___x_548_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_ctorIdx___boxed(lean_object* v_x_549_){
_start:
{
uint8_t v_x_boxed_550_; lean_object* v_res_551_; 
v_x_boxed_550_ = lean_unbox(v_x_549_);
v_res_551_ = lp_orb_x2dcompiler_Pancake_Binop_ctorIdx(v_x_boxed_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_toCtorIdx(uint8_t v_x_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = lp_orb_x2dcompiler_Pancake_Binop_ctorIdx(v_x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_toCtorIdx___boxed(lean_object* v_x_554_){
_start:
{
uint8_t v_x_4__boxed_555_; lean_object* v_res_556_; 
v_x_4__boxed_555_ = lean_unbox(v_x_554_);
v_res_556_ = lp_orb_x2dcompiler_Pancake_Binop_toCtorIdx(v_x_4__boxed_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_ctorElim___redArg(lean_object* v_k_557_){
_start:
{
lean_inc(v_k_557_);
return v_k_557_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_ctorElim___redArg___boxed(lean_object* v_k_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = lp_orb_x2dcompiler_Pancake_Binop_ctorElim___redArg(v_k_558_);
lean_dec(v_k_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_ctorElim(lean_object* v_motive_560_, lean_object* v_ctorIdx_561_, uint8_t v_t_562_, lean_object* v_h_563_, lean_object* v_k_564_){
_start:
{
lean_inc(v_k_564_);
return v_k_564_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_ctorElim___boxed(lean_object* v_motive_565_, lean_object* v_ctorIdx_566_, lean_object* v_t_567_, lean_object* v_h_568_, lean_object* v_k_569_){
_start:
{
uint8_t v_t_boxed_570_; lean_object* v_res_571_; 
v_t_boxed_570_ = lean_unbox(v_t_567_);
v_res_571_ = lp_orb_x2dcompiler_Pancake_Binop_ctorElim(v_motive_565_, v_ctorIdx_566_, v_t_boxed_570_, v_h_568_, v_k_569_);
lean_dec(v_k_569_);
lean_dec(v_ctorIdx_566_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_add_elim___redArg(lean_object* v_add_572_){
_start:
{
lean_inc(v_add_572_);
return v_add_572_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_add_elim___redArg___boxed(lean_object* v_add_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = lp_orb_x2dcompiler_Pancake_Binop_add_elim___redArg(v_add_573_);
lean_dec(v_add_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_add_elim(lean_object* v_motive_575_, uint8_t v_t_576_, lean_object* v_h_577_, lean_object* v_add_578_){
_start:
{
lean_inc(v_add_578_);
return v_add_578_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_add_elim___boxed(lean_object* v_motive_579_, lean_object* v_t_580_, lean_object* v_h_581_, lean_object* v_add_582_){
_start:
{
uint8_t v_t_boxed_583_; lean_object* v_res_584_; 
v_t_boxed_583_ = lean_unbox(v_t_580_);
v_res_584_ = lp_orb_x2dcompiler_Pancake_Binop_add_elim(v_motive_579_, v_t_boxed_583_, v_h_581_, v_add_582_);
lean_dec(v_add_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_and___00elim___redArg(lean_object* v_and___585_){
_start:
{
lean_inc(v_and___585_);
return v_and___585_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_and___00elim___redArg___boxed(lean_object* v_and___586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = lp_orb_x2dcompiler_Pancake_Binop_and___00elim___redArg(v_and___586_);
lean_dec(v_and___586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_and___00elim(lean_object* v_motive_588_, uint8_t v_t_589_, lean_object* v_h_590_, lean_object* v_and___591_){
_start:
{
lean_inc(v_and___591_);
return v_and___591_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_and___00elim___boxed(lean_object* v_motive_592_, lean_object* v_t_593_, lean_object* v_h_594_, lean_object* v_and___595_){
_start:
{
uint8_t v_t_boxed_596_; lean_object* v_res_597_; 
v_t_boxed_596_ = lean_unbox(v_t_593_);
v_res_597_ = lp_orb_x2dcompiler_Pancake_Binop_and___00elim(v_motive_592_, v_t_boxed_596_, v_h_594_, v_and___595_);
lean_dec(v_and___595_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_sub_elim___redArg(lean_object* v_sub_598_){
_start:
{
lean_inc(v_sub_598_);
return v_sub_598_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_sub_elim___redArg___boxed(lean_object* v_sub_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = lp_orb_x2dcompiler_Pancake_Binop_sub_elim___redArg(v_sub_599_);
lean_dec(v_sub_599_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_sub_elim(lean_object* v_motive_601_, uint8_t v_t_602_, lean_object* v_h_603_, lean_object* v_sub_604_){
_start:
{
lean_inc(v_sub_604_);
return v_sub_604_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_sub_elim___boxed(lean_object* v_motive_605_, lean_object* v_t_606_, lean_object* v_h_607_, lean_object* v_sub_608_){
_start:
{
uint8_t v_t_boxed_609_; lean_object* v_res_610_; 
v_t_boxed_609_ = lean_unbox(v_t_606_);
v_res_610_ = lp_orb_x2dcompiler_Pancake_Binop_sub_elim(v_motive_605_, v_t_boxed_609_, v_h_607_, v_sub_608_);
lean_dec(v_sub_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprBinop_repr(uint8_t v_x_620_, lean_object* v_prec_621_){
_start:
{
lean_object* v___y_623_; lean_object* v___y_630_; lean_object* v___y_637_; 
switch(v_x_620_)
{
case 0:
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_unsigned_to_nat(1024u);
v___x_644_ = lean_nat_dec_le(v___x_643_, v_prec_621_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
v___x_645_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_623_ = v___x_645_;
goto v___jp_622_;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_623_ = v___x_646_;
goto v___jp_622_;
}
}
case 1:
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_unsigned_to_nat(1024u);
v___x_648_ = lean_nat_dec_le(v___x_647_, v_prec_621_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; 
v___x_649_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_630_ = v___x_649_;
goto v___jp_629_;
}
else
{
lean_object* v___x_650_; 
v___x_650_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_630_ = v___x_650_;
goto v___jp_629_;
}
}
default: 
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(1024u);
v___x_652_ = lean_nat_dec_le(v___x_651_, v_prec_621_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
v___x_653_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_637_ = v___x_653_;
goto v___jp_636_;
}
else
{
lean_object* v___x_654_; 
v___x_654_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_637_ = v___x_654_;
goto v___jp_636_;
}
}
}
v___jp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_624_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__1));
lean_inc(v___y_623_);
v___x_625_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_625_, 0, v___y_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = 0;
v___x_627_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set_uint8(v___x_627_, sizeof(void*)*1, v___x_626_);
v___x_628_ = l_Repr_addAppParen(v___x_627_, v_prec_621_);
return v___x_628_;
}
v___jp_629_:
{
lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_631_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__3));
lean_inc(v___y_630_);
v___x_632_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_632_, 0, v___y_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = 0;
v___x_634_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set_uint8(v___x_634_, sizeof(void*)*1, v___x_633_);
v___x_635_ = l_Repr_addAppParen(v___x_634_, v_prec_621_);
return v___x_635_;
}
v___jp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_638_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprBinop_repr___closed__5));
lean_inc(v___y_637_);
v___x_639_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_639_, 0, v___y_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = 0;
v___x_641_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*1, v___x_640_);
v___x_642_ = l_Repr_addAppParen(v___x_641_, v_prec_621_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprBinop_repr___boxed(lean_object* v_x_655_, lean_object* v_prec_656_){
_start:
{
uint8_t v_x_173__boxed_657_; lean_object* v_res_658_; 
v_x_173__boxed_657_ = lean_unbox(v_x_655_);
v_res_658_ = lp_orb_x2dcompiler_Pancake_instReprBinop_repr(v_x_173__boxed_657_, v_prec_656_);
lean_dec(v_prec_656_);
return v_res_658_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_Binop_ofNat(lean_object* v_n_661_){
_start:
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_nat_dec_le(v_n_661_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = lean_nat_dec_le(v_n_661_, v___x_664_);
if (v___x_665_ == 0)
{
uint8_t v___x_666_; 
v___x_666_ = 2;
return v___x_666_;
}
else
{
uint8_t v___x_667_; 
v___x_667_ = 1;
return v___x_667_;
}
}
else
{
uint8_t v___x_668_; 
v___x_668_ = 0;
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Binop_ofNat___boxed(lean_object* v_n_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = lp_orb_x2dcompiler_Pancake_Binop_ofNat(v_n_669_);
lean_dec(v_n_669_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_instDecidableEqBinop(uint8_t v_x_672_, uint8_t v_y_673_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_674_ = lp_orb_x2dcompiler_Pancake_Binop_ctorIdx(v_x_672_);
v___x_675_ = lp_orb_x2dcompiler_Pancake_Binop_ctorIdx(v_y_673_);
v___x_676_ = lean_nat_dec_eq(v___x_674_, v___x_675_);
lean_dec(v___x_675_);
lean_dec(v___x_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instDecidableEqBinop___boxed(lean_object* v_x_677_, lean_object* v_y_678_){
_start:
{
uint8_t v_x_13__boxed_679_; uint8_t v_y_14__boxed_680_; uint8_t v_res_681_; lean_object* v_r_682_; 
v_x_13__boxed_679_ = lean_unbox(v_x_677_);
v_y_14__boxed_680_ = lean_unbox(v_y_678_);
v_res_681_ = lp_orb_x2dcompiler_Pancake_instDecidableEqBinop(v_x_13__boxed_679_, v_y_14__boxed_680_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_ctorIdx(uint8_t v_x_683_){
_start:
{
switch(v_x_683_)
{
case 0:
{
lean_object* v___x_684_; 
v___x_684_ = lean_unsigned_to_nat(0u);
return v___x_684_;
}
case 1:
{
lean_object* v___x_685_; 
v___x_685_ = lean_unsigned_to_nat(1u);
return v___x_685_;
}
default: 
{
lean_object* v___x_686_; 
v___x_686_ = lean_unsigned_to_nat(2u);
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_ctorIdx___boxed(lean_object* v_x_687_){
_start:
{
uint8_t v_x_boxed_688_; lean_object* v_res_689_; 
v_x_boxed_688_ = lean_unbox(v_x_687_);
v_res_689_ = lp_orb_x2dcompiler_Pancake_Cmp_ctorIdx(v_x_boxed_688_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_toCtorIdx(uint8_t v_x_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = lp_orb_x2dcompiler_Pancake_Cmp_ctorIdx(v_x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_toCtorIdx___boxed(lean_object* v_x_692_){
_start:
{
uint8_t v_x_4__boxed_693_; lean_object* v_res_694_; 
v_x_4__boxed_693_ = lean_unbox(v_x_692_);
v_res_694_ = lp_orb_x2dcompiler_Pancake_Cmp_toCtorIdx(v_x_4__boxed_693_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_ctorElim___redArg(lean_object* v_k_695_){
_start:
{
lean_inc(v_k_695_);
return v_k_695_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_ctorElim___redArg___boxed(lean_object* v_k_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = lp_orb_x2dcompiler_Pancake_Cmp_ctorElim___redArg(v_k_696_);
lean_dec(v_k_696_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_ctorElim(lean_object* v_motive_698_, lean_object* v_ctorIdx_699_, uint8_t v_t_700_, lean_object* v_h_701_, lean_object* v_k_702_){
_start:
{
lean_inc(v_k_702_);
return v_k_702_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_ctorElim___boxed(lean_object* v_motive_703_, lean_object* v_ctorIdx_704_, lean_object* v_t_705_, lean_object* v_h_706_, lean_object* v_k_707_){
_start:
{
uint8_t v_t_boxed_708_; lean_object* v_res_709_; 
v_t_boxed_708_ = lean_unbox(v_t_705_);
v_res_709_ = lp_orb_x2dcompiler_Pancake_Cmp_ctorElim(v_motive_703_, v_ctorIdx_704_, v_t_boxed_708_, v_h_706_, v_k_707_);
lean_dec(v_k_707_);
lean_dec(v_ctorIdx_704_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_less_elim___redArg(lean_object* v_less_710_){
_start:
{
lean_inc(v_less_710_);
return v_less_710_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_less_elim___redArg___boxed(lean_object* v_less_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = lp_orb_x2dcompiler_Pancake_Cmp_less_elim___redArg(v_less_711_);
lean_dec(v_less_711_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_less_elim(lean_object* v_motive_713_, uint8_t v_t_714_, lean_object* v_h_715_, lean_object* v_less_716_){
_start:
{
lean_inc(v_less_716_);
return v_less_716_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_less_elim___boxed(lean_object* v_motive_717_, lean_object* v_t_718_, lean_object* v_h_719_, lean_object* v_less_720_){
_start:
{
uint8_t v_t_boxed_721_; lean_object* v_res_722_; 
v_t_boxed_721_ = lean_unbox(v_t_718_);
v_res_722_ = lp_orb_x2dcompiler_Pancake_Cmp_less_elim(v_motive_717_, v_t_boxed_721_, v_h_719_, v_less_720_);
lean_dec(v_less_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_equal_elim___redArg(lean_object* v_equal_723_){
_start:
{
lean_inc(v_equal_723_);
return v_equal_723_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_equal_elim___redArg___boxed(lean_object* v_equal_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = lp_orb_x2dcompiler_Pancake_Cmp_equal_elim___redArg(v_equal_724_);
lean_dec(v_equal_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_equal_elim(lean_object* v_motive_726_, uint8_t v_t_727_, lean_object* v_h_728_, lean_object* v_equal_729_){
_start:
{
lean_inc(v_equal_729_);
return v_equal_729_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_equal_elim___boxed(lean_object* v_motive_730_, lean_object* v_t_731_, lean_object* v_h_732_, lean_object* v_equal_733_){
_start:
{
uint8_t v_t_boxed_734_; lean_object* v_res_735_; 
v_t_boxed_734_ = lean_unbox(v_t_731_);
v_res_735_ = lp_orb_x2dcompiler_Pancake_Cmp_equal_elim(v_motive_730_, v_t_boxed_734_, v_h_732_, v_equal_733_);
lean_dec(v_equal_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_notLess_elim___redArg(lean_object* v_notLess_736_){
_start:
{
lean_inc(v_notLess_736_);
return v_notLess_736_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_notLess_elim___redArg___boxed(lean_object* v_notLess_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = lp_orb_x2dcompiler_Pancake_Cmp_notLess_elim___redArg(v_notLess_737_);
lean_dec(v_notLess_737_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_notLess_elim(lean_object* v_motive_739_, uint8_t v_t_740_, lean_object* v_h_741_, lean_object* v_notLess_742_){
_start:
{
lean_inc(v_notLess_742_);
return v_notLess_742_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_notLess_elim___boxed(lean_object* v_motive_743_, lean_object* v_t_744_, lean_object* v_h_745_, lean_object* v_notLess_746_){
_start:
{
uint8_t v_t_boxed_747_; lean_object* v_res_748_; 
v_t_boxed_747_ = lean_unbox(v_t_744_);
v_res_748_ = lp_orb_x2dcompiler_Pancake_Cmp_notLess_elim(v_motive_743_, v_t_boxed_747_, v_h_745_, v_notLess_746_);
lean_dec(v_notLess_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprCmp_repr(uint8_t v_x_758_, lean_object* v_prec_759_){
_start:
{
lean_object* v___y_761_; lean_object* v___y_768_; lean_object* v___y_775_; 
switch(v_x_758_)
{
case 0:
{
lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(1024u);
v___x_782_ = lean_nat_dec_le(v___x_781_, v_prec_759_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; 
v___x_783_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_761_ = v___x_783_;
goto v___jp_760_;
}
else
{
lean_object* v___x_784_; 
v___x_784_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_761_ = v___x_784_;
goto v___jp_760_;
}
}
case 1:
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = lean_unsigned_to_nat(1024u);
v___x_786_ = lean_nat_dec_le(v___x_785_, v_prec_759_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; 
v___x_787_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_768_ = v___x_787_;
goto v___jp_767_;
}
else
{
lean_object* v___x_788_; 
v___x_788_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_768_ = v___x_788_;
goto v___jp_767_;
}
}
default: 
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = lean_unsigned_to_nat(1024u);
v___x_790_ = lean_nat_dec_le(v___x_789_, v_prec_759_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
v___x_791_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_775_ = v___x_791_;
goto v___jp_774_;
}
else
{
lean_object* v___x_792_; 
v___x_792_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_775_ = v___x_792_;
goto v___jp_774_;
}
}
}
v___jp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_762_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__1));
lean_inc(v___y_761_);
v___x_763_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_763_, 0, v___y_761_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = 0;
v___x_765_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set_uint8(v___x_765_, sizeof(void*)*1, v___x_764_);
v___x_766_ = l_Repr_addAppParen(v___x_765_, v_prec_759_);
return v___x_766_;
}
v___jp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_769_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__3));
lean_inc(v___y_768_);
v___x_770_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_770_, 0, v___y_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = 0;
v___x_772_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*1, v___x_771_);
v___x_773_ = l_Repr_addAppParen(v___x_772_, v_prec_759_);
return v___x_773_;
}
v___jp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_776_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprCmp_repr___closed__5));
lean_inc(v___y_775_);
v___x_777_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_777_, 0, v___y_775_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = 0;
v___x_779_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*1, v___x_778_);
v___x_780_ = l_Repr_addAppParen(v___x_779_, v_prec_759_);
return v___x_780_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprCmp_repr___boxed(lean_object* v_x_793_, lean_object* v_prec_794_){
_start:
{
uint8_t v_x_173__boxed_795_; lean_object* v_res_796_; 
v_x_173__boxed_795_ = lean_unbox(v_x_793_);
v_res_796_ = lp_orb_x2dcompiler_Pancake_instReprCmp_repr(v_x_173__boxed_795_, v_prec_794_);
lean_dec(v_prec_794_);
return v_res_796_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_Cmp_ofNat(lean_object* v_n_799_){
_start:
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_nat_dec_le(v_n_799_, v___x_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_802_ = lean_unsigned_to_nat(1u);
v___x_803_ = lean_nat_dec_le(v_n_799_, v___x_802_);
if (v___x_803_ == 0)
{
uint8_t v___x_804_; 
v___x_804_ = 2;
return v___x_804_;
}
else
{
uint8_t v___x_805_; 
v___x_805_ = 1;
return v___x_805_;
}
}
else
{
uint8_t v___x_806_; 
v___x_806_ = 0;
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_Cmp_ofNat___boxed(lean_object* v_n_807_){
_start:
{
uint8_t v_res_808_; lean_object* v_r_809_; 
v_res_808_ = lp_orb_x2dcompiler_Pancake_Cmp_ofNat(v_n_807_);
lean_dec(v_n_807_);
v_r_809_ = lean_box(v_res_808_);
return v_r_809_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_instDecidableEqCmp(uint8_t v_x_810_, uint8_t v_y_811_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_812_ = lp_orb_x2dcompiler_Pancake_Cmp_ctorIdx(v_x_810_);
v___x_813_ = lp_orb_x2dcompiler_Pancake_Cmp_ctorIdx(v_y_811_);
v___x_814_ = lean_nat_dec_eq(v___x_812_, v___x_813_);
lean_dec(v___x_813_);
lean_dec(v___x_812_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instDecidableEqCmp___boxed(lean_object* v_x_815_, lean_object* v_y_816_){
_start:
{
uint8_t v_x_13__boxed_817_; uint8_t v_y_14__boxed_818_; uint8_t v_res_819_; lean_object* v_r_820_; 
v_x_13__boxed_817_ = lean_unbox(v_x_815_);
v_y_14__boxed_818_ = lean_unbox(v_y_816_);
v_res_819_ = lp_orb_x2dcompiler_Pancake_instDecidableEqCmp(v_x_13__boxed_817_, v_y_14__boxed_818_);
v_r_820_ = lean_box(v_res_819_);
return v_r_820_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_ctorIdx(lean_object* v_x_821_){
_start:
{
switch(lean_obj_tag(v_x_821_))
{
case 0:
{
lean_object* v___x_822_; 
v___x_822_ = lean_unsigned_to_nat(0u);
return v___x_822_;
}
case 1:
{
lean_object* v___x_823_; 
v___x_823_ = lean_unsigned_to_nat(1u);
return v___x_823_;
}
case 2:
{
lean_object* v___x_824_; 
v___x_824_ = lean_unsigned_to_nat(2u);
return v___x_824_;
}
case 3:
{
lean_object* v___x_825_; 
v___x_825_ = lean_unsigned_to_nat(3u);
return v___x_825_;
}
case 4:
{
lean_object* v___x_826_; 
v___x_826_ = lean_unsigned_to_nat(4u);
return v___x_826_;
}
case 5:
{
lean_object* v___x_827_; 
v___x_827_ = lean_unsigned_to_nat(5u);
return v___x_827_;
}
case 6:
{
lean_object* v___x_828_; 
v___x_828_ = lean_unsigned_to_nat(6u);
return v___x_828_;
}
default: 
{
lean_object* v___x_829_; 
v___x_829_ = lean_unsigned_to_nat(7u);
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_ctorIdx___boxed(lean_object* v_x_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorIdx(v_x_830_);
lean_dec(v_x_830_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(lean_object* v_t_832_, lean_object* v_k_833_){
_start:
{
switch(lean_obj_tag(v_t_832_))
{
case 1:
{
lean_object* v_name_834_; lean_object* v___x_835_; 
v_name_834_ = lean_ctor_get(v_t_832_, 0);
lean_inc_ref(v_name_834_);
lean_dec_ref(v_t_832_);
v___x_835_ = lean_apply_1(v_k_833_, v_name_834_);
return v___x_835_;
}
case 2:
{
return v_k_833_;
}
case 3:
{
uint8_t v_bop_836_; lean_object* v_l_837_; lean_object* v_r_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_bop_836_ = lean_ctor_get_uint8(v_t_832_, sizeof(void*)*2);
v_l_837_ = lean_ctor_get(v_t_832_, 0);
lean_inc(v_l_837_);
v_r_838_ = lean_ctor_get(v_t_832_, 1);
lean_inc(v_r_838_);
lean_dec_ref(v_t_832_);
v___x_839_ = lean_box(v_bop_836_);
v___x_840_ = lean_apply_3(v_k_833_, v___x_839_, v_l_837_, v_r_838_);
return v___x_840_;
}
case 4:
{
lean_object* v_l_841_; lean_object* v_r_842_; lean_object* v___x_843_; 
v_l_841_ = lean_ctor_get(v_t_832_, 0);
lean_inc(v_l_841_);
v_r_842_ = lean_ctor_get(v_t_832_, 1);
lean_inc(v_r_842_);
lean_dec_ref(v_t_832_);
v___x_843_ = lean_apply_2(v_k_833_, v_l_841_, v_r_842_);
return v___x_843_;
}
case 5:
{
uint8_t v_c_844_; lean_object* v_l_845_; lean_object* v_r_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_c_844_ = lean_ctor_get_uint8(v_t_832_, sizeof(void*)*2);
v_l_845_ = lean_ctor_get(v_t_832_, 0);
lean_inc(v_l_845_);
v_r_846_ = lean_ctor_get(v_t_832_, 1);
lean_inc(v_r_846_);
lean_dec_ref(v_t_832_);
v___x_847_ = lean_box(v_c_844_);
v___x_848_ = lean_apply_3(v_k_833_, v___x_847_, v_l_845_, v_r_846_);
return v___x_848_;
}
default: 
{
lean_object* v_w_849_; lean_object* v___x_850_; 
v_w_849_ = lean_ctor_get(v_t_832_, 0);
lean_inc(v_w_849_);
lean_dec(v_t_832_);
v___x_850_ = lean_apply_1(v_k_833_, v_w_849_);
return v___x_850_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim(lean_object* v_motive_851_, lean_object* v_ctorIdx_852_, lean_object* v_t_853_, lean_object* v_h_854_, lean_object* v_k_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_853_, v_k_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___boxed(lean_object* v_motive_857_, lean_object* v_ctorIdx_858_, lean_object* v_t_859_, lean_object* v_h_860_, lean_object* v_k_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim(v_motive_857_, v_ctorIdx_858_, v_t_859_, v_h_860_, v_k_861_);
lean_dec(v_ctorIdx_858_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_const_elim___redArg(lean_object* v_t_863_, lean_object* v_const_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_863_, v_const_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_const_elim(lean_object* v_motive_866_, lean_object* v_t_867_, lean_object* v_h_868_, lean_object* v_const_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_867_, v_const_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_var_elim___redArg(lean_object* v_t_871_, lean_object* v_var_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_871_, v_var_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_var_elim(lean_object* v_motive_874_, lean_object* v_t_875_, lean_object* v_h_876_, lean_object* v_var_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_875_, v_var_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_base_elim___redArg(lean_object* v_t_879_, lean_object* v_base_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_879_, v_base_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_base_elim(lean_object* v_motive_882_, lean_object* v_t_883_, lean_object* v_h_884_, lean_object* v_base_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_883_, v_base_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_op_elim___redArg(lean_object* v_t_887_, lean_object* v_op_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_887_, v_op_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_op_elim(lean_object* v_motive_890_, lean_object* v_t_891_, lean_object* v_h_892_, lean_object* v_op_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_891_, v_op_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_mul_elim___redArg(lean_object* v_t_895_, lean_object* v_mul_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_895_, v_mul_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_mul_elim(lean_object* v_motive_898_, lean_object* v_t_899_, lean_object* v_h_900_, lean_object* v_mul_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_899_, v_mul_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_cmp_elim___redArg(lean_object* v_t_903_, lean_object* v_cmp_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_903_, v_cmp_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_cmp_elim(lean_object* v_motive_906_, lean_object* v_t_907_, lean_object* v_h_908_, lean_object* v_cmp_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_907_, v_cmp_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_loadByte_elim___redArg(lean_object* v_t_911_, lean_object* v_loadByte_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_911_, v_loadByte_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_loadByte_elim(lean_object* v_motive_914_, lean_object* v_t_915_, lean_object* v_h_916_, lean_object* v_loadByte_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_915_, v_loadByte_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_loadWord_elim___redArg(lean_object* v_t_919_, lean_object* v_loadWord_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_919_, v_loadWord_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeExp_loadWord_elim(lean_object* v_motive_922_, lean_object* v_t_923_, lean_object* v_h_924_, lean_object* v_loadWord_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = lp_orb_x2dcompiler_Pancake_PancakeExp_ctorElim___redArg(v_t_923_, v_loadWord_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(lean_object* v_x_972_, lean_object* v_prec_973_){
_start:
{
lean_object* v___y_975_; 
switch(lean_obj_tag(v_x_972_))
{
case 0:
{
lean_object* v_w_981_; lean_object* v___y_983_; lean_object* v___x_992_; uint8_t v___x_993_; 
v_w_981_ = lean_ctor_get(v_x_972_, 0);
lean_inc(v_w_981_);
lean_dec_ref(v_x_972_);
v___x_992_ = lean_unsigned_to_nat(1024u);
v___x_993_ = lean_nat_dec_le(v___x_992_, v_prec_973_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
v___x_994_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_983_ = v___x_994_;
goto v___jp_982_;
}
else
{
lean_object* v___x_995_; 
v___x_995_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_983_ = v___x_995_;
goto v___jp_982_;
}
v___jp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_984_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__4));
v___x_985_ = lean_unsigned_to_nat(64u);
v___x_986_ = l_BitVec_repr(v___x_985_, v_w_981_);
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_984_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
lean_inc(v___y_983_);
v___x_988_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_988_, 0, v___y_983_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = 0;
v___x_990_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set_uint8(v___x_990_, sizeof(void*)*1, v___x_989_);
v___x_991_ = l_Repr_addAppParen(v___x_990_, v_prec_973_);
return v___x_991_;
}
}
case 1:
{
lean_object* v_name_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1016_; 
v_name_996_ = lean_ctor_get(v_x_972_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_998_ = v_x_972_;
v_isShared_999_ = v_isSharedCheck_1016_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_name_996_);
lean_dec(v_x_972_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1016_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___y_1001_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = lean_unsigned_to_nat(1024u);
v___x_1013_ = lean_nat_dec_le(v___x_1012_, v_prec_973_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1001_ = v___x_1014_;
goto v___jp_1000_;
}
else
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1001_ = v___x_1015_;
goto v___jp_1000_;
}
v___jp_1000_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1002_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__7));
v___x_1003_ = l_String_quote(v_name_996_);
if (v_isShared_999_ == 0)
{
lean_ctor_set_tag(v___x_998_, 3);
lean_ctor_set(v___x_998_, 0, v___x_1003_);
v___x_1005_ = v___x_998_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1002_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
lean_inc(v___y_1001_);
v___x_1007_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___y_1001_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = 0;
v___x_1009_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*1, v___x_1008_);
v___x_1010_ = l_Repr_addAppParen(v___x_1009_, v_prec_973_);
return v___x_1010_;
}
}
}
}
case 2:
{
lean_object* v___x_1017_; uint8_t v___x_1018_; 
v___x_1017_ = lean_unsigned_to_nat(1024u);
v___x_1018_ = lean_nat_dec_le(v___x_1017_, v_prec_973_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_975_ = v___x_1019_;
goto v___jp_974_;
}
else
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_975_ = v___x_1020_;
goto v___jp_974_;
}
}
case 3:
{
uint8_t v_bop_1021_; lean_object* v_l_1022_; lean_object* v_r_1023_; lean_object* v___x_1024_; lean_object* v___y_1026_; uint8_t v___x_1041_; 
v_bop_1021_ = lean_ctor_get_uint8(v_x_972_, sizeof(void*)*2);
v_l_1022_ = lean_ctor_get(v_x_972_, 0);
lean_inc(v_l_1022_);
v_r_1023_ = lean_ctor_get(v_x_972_, 1);
lean_inc(v_r_1023_);
lean_dec_ref(v_x_972_);
v___x_1024_ = lean_unsigned_to_nat(1024u);
v___x_1041_ = lean_nat_dec_le(v___x_1024_, v_prec_973_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1026_ = v___x_1042_;
goto v___jp_1025_;
}
else
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1026_ = v___x_1043_;
goto v___jp_1025_;
}
v___jp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1027_ = lean_box(1);
v___x_1028_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__10));
v___x_1029_ = lp_orb_x2dcompiler_Pancake_instReprBinop_repr(v_bop_1021_, v___x_1024_);
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_1027_);
v___x_1032_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_l_1022_, v___x_1024_);
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v___x_1027_);
v___x_1035_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_r_1023_, v___x_1024_);
v___x_1036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
lean_inc(v___y_1026_);
v___x_1037_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___y_1026_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = 0;
v___x_1039_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set_uint8(v___x_1039_, sizeof(void*)*1, v___x_1038_);
v___x_1040_ = l_Repr_addAppParen(v___x_1039_, v_prec_973_);
return v___x_1040_;
}
}
case 4:
{
lean_object* v_l_1044_; lean_object* v_r_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1068_; 
v_l_1044_ = lean_ctor_get(v_x_972_, 0);
v_r_1045_ = lean_ctor_get(v_x_972_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1047_ = v_x_972_;
v_isShared_1048_ = v_isSharedCheck_1068_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_r_1045_);
lean_inc(v_l_1044_);
lean_dec(v_x_972_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1068_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___y_1051_; uint8_t v___x_1065_; 
v___x_1049_ = lean_unsigned_to_nat(1024u);
v___x_1065_ = lean_nat_dec_le(v___x_1049_, v_prec_973_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1051_ = v___x_1066_;
goto v___jp_1050_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1051_ = v___x_1067_;
goto v___jp_1050_;
}
v___jp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1052_ = lean_box(1);
v___x_1053_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__13));
v___x_1054_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_l_1044_, v___x_1049_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 5);
lean_ctor_set(v___x_1047_, 1, v___x_1054_);
lean_ctor_set(v___x_1047_, 0, v___x_1053_);
v___x_1056_ = v___x_1047_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v___x_1052_);
v___x_1058_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_r_1045_, v___x_1049_);
v___x_1059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
lean_inc(v___y_1051_);
v___x_1060_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___y_1051_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = 0;
v___x_1062_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set_uint8(v___x_1062_, sizeof(void*)*1, v___x_1061_);
v___x_1063_ = l_Repr_addAppParen(v___x_1062_, v_prec_973_);
return v___x_1063_;
}
}
}
}
case 5:
{
uint8_t v_c_1069_; lean_object* v_l_1070_; lean_object* v_r_1071_; lean_object* v___x_1072_; lean_object* v___y_1074_; uint8_t v___x_1089_; 
v_c_1069_ = lean_ctor_get_uint8(v_x_972_, sizeof(void*)*2);
v_l_1070_ = lean_ctor_get(v_x_972_, 0);
lean_inc(v_l_1070_);
v_r_1071_ = lean_ctor_get(v_x_972_, 1);
lean_inc(v_r_1071_);
lean_dec_ref(v_x_972_);
v___x_1072_ = lean_unsigned_to_nat(1024u);
v___x_1089_ = lean_nat_dec_le(v___x_1072_, v_prec_973_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1074_ = v___x_1090_;
goto v___jp_1073_;
}
else
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1074_ = v___x_1091_;
goto v___jp_1073_;
}
v___jp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1075_ = lean_box(1);
v___x_1076_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__16));
v___x_1077_ = lp_orb_x2dcompiler_Pancake_instReprCmp_repr(v_c_1069_, v___x_1072_);
v___x_1078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v___x_1075_);
v___x_1080_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_l_1070_, v___x_1072_);
v___x_1081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v___x_1075_);
v___x_1083_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_r_1071_, v___x_1072_);
v___x_1084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
lean_inc(v___y_1074_);
v___x_1085_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___y_1074_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = 0;
v___x_1087_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*1, v___x_1086_);
v___x_1088_ = l_Repr_addAppParen(v___x_1087_, v_prec_973_);
return v___x_1088_;
}
}
case 6:
{
lean_object* v_addr_1092_; lean_object* v___x_1093_; lean_object* v___y_1095_; uint8_t v___x_1103_; 
v_addr_1092_ = lean_ctor_get(v_x_972_, 0);
lean_inc(v_addr_1092_);
lean_dec_ref(v_x_972_);
v___x_1093_ = lean_unsigned_to_nat(1024u);
v___x_1103_ = lean_nat_dec_le(v___x_1093_, v_prec_973_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1095_ = v___x_1104_;
goto v___jp_1094_;
}
else
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1095_ = v___x_1105_;
goto v___jp_1094_;
}
v___jp_1094_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1096_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__19));
v___x_1097_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_addr_1092_, v___x_1093_);
v___x_1098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
lean_inc(v___y_1095_);
v___x_1099_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___y_1095_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = 0;
v___x_1101_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*1, v___x_1100_);
v___x_1102_ = l_Repr_addAppParen(v___x_1101_, v_prec_973_);
return v___x_1102_;
}
}
default: 
{
lean_object* v_addr_1106_; lean_object* v___x_1107_; lean_object* v___y_1109_; uint8_t v___x_1117_; 
v_addr_1106_ = lean_ctor_get(v_x_972_, 0);
lean_inc(v_addr_1106_);
lean_dec_ref(v_x_972_);
v___x_1107_ = lean_unsigned_to_nat(1024u);
v___x_1117_ = lean_nat_dec_le(v___x_1107_, v_prec_973_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1109_ = v___x_1118_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1109_ = v___x_1119_;
goto v___jp_1108_;
}
v___jp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1110_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__22));
v___x_1111_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_addr_1106_, v___x_1107_);
v___x_1112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
lean_inc(v___y_1109_);
v___x_1113_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___y_1109_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = 0;
v___x_1115_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1115_, 0, v___x_1113_);
lean_ctor_set_uint8(v___x_1115_, sizeof(void*)*1, v___x_1114_);
v___x_1116_ = l_Repr_addAppParen(v___x_1115_, v_prec_973_);
return v___x_1116_;
}
}
}
v___jp_974_:
{
lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_976_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___closed__1));
lean_inc(v___y_975_);
v___x_977_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_977_, 0, v___y_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = 0;
v___x_979_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set_uint8(v___x_979_, sizeof(void*)*1, v___x_978_);
v___x_980_ = l_Repr_addAppParen(v___x_979_, v_prec_973_);
return v___x_980_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr___boxed(lean_object* v_x_1120_, lean_object* v_prec_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_x_1120_, v_prec_1121_);
lean_dec(v_prec_1121_);
return v_res_1122_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_signedLt(lean_object* v_a_1125_, lean_object* v_b_1126_){
_start:
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = lean_unsigned_to_nat(64u);
v___x_1128_ = l_BitVec_slt(v___x_1127_, v_a_1125_, v_b_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_signedLt___boxed(lean_object* v_a_1129_, lean_object* v_b_1130_){
_start:
{
uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = lp_orb_x2dcompiler_Pancake_signedLt(v_a_1129_, v_b_1130_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_eval___redArg___closed__0(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_unsigned_to_nat(64u);
v___x_1135_ = l_BitVec_ofNat(v___x_1134_, v___x_1133_);
return v___x_1135_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_eval___redArg___closed__1(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_eval___redArg___closed__0, &lp_orb_x2dcompiler_Pancake_eval___redArg___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_eval___redArg___closed__0);
v___x_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_eval___redArg___closed__2(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_wordSliceAlt___closed__0, &lp_orb_x2dcompiler_Pancake_wordSliceAlt___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_wordSliceAlt___closed__0);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_eval___redArg(lean_object* v_s_1140_, lean_object* v_x_1141_){
_start:
{
switch(lean_obj_tag(v_x_1141_))
{
case 0:
{
lean_object* v_w_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v_s_1140_);
v_w_1142_ = lean_ctor_get(v_x_1141_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_x_1141_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v_x_1141_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_w_1142_);
lean_dec(v_x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set_tag(v___x_1144_, 1);
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_w_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
case 1:
{
lean_object* v_name_1150_; lean_object* v_locals_1151_; lean_object* v___x_1152_; 
v_name_1150_ = lean_ctor_get(v_x_1141_, 0);
lean_inc_ref(v_name_1150_);
lean_dec_ref(v_x_1141_);
v_locals_1151_ = lean_ctor_get(v_s_1140_, 0);
lean_inc_ref(v_locals_1151_);
lean_dec_ref(v_s_1140_);
v___x_1152_ = lean_apply_1(v_locals_1151_, v_name_1150_);
return v___x_1152_;
}
case 2:
{
lean_object* v_baseAddr_1153_; lean_object* v___x_1154_; 
v_baseAddr_1153_ = lean_ctor_get(v_s_1140_, 5);
lean_inc(v_baseAddr_1153_);
lean_dec_ref(v_s_1140_);
v___x_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_baseAddr_1153_);
return v___x_1154_;
}
case 3:
{
uint8_t v_bop_1155_; lean_object* v_l_1156_; lean_object* v_r_1157_; lean_object* v___x_1158_; 
v_bop_1155_ = lean_ctor_get_uint8(v_x_1141_, sizeof(void*)*2);
v_l_1156_ = lean_ctor_get(v_x_1141_, 0);
lean_inc(v_l_1156_);
v_r_1157_ = lean_ctor_get(v_x_1141_, 1);
lean_inc(v_r_1157_);
lean_dec_ref(v_x_1141_);
lean_inc_ref(v_s_1140_);
v___x_1158_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_s_1140_, v_l_1156_);
if (lean_obj_tag(v___x_1158_) == 1)
{
lean_object* v_val_1159_; lean_object* v___x_1160_; 
v_val_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_val_1159_);
lean_dec_ref(v___x_1158_);
v___x_1160_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_s_1140_, v_r_1157_);
if (lean_obj_tag(v___x_1160_) == 1)
{
switch(v_bop_1155_)
{
case 0:
{
lean_object* v_val_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1170_; 
v_val_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1170_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_val_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1170_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1165_ = lean_unsigned_to_nat(64u);
v___x_1166_ = l_BitVec_add(v___x_1165_, v_val_1159_, v_val_1161_);
lean_dec(v_val_1161_);
lean_dec(v_val_1159_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1166_);
v___x_1168_ = v___x_1163_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
case 1:
{
lean_object* v_val_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1179_; 
v_val_1171_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1173_ = v___x_1160_;
v_isShared_1174_ = v_isSharedCheck_1179_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_val_1171_);
lean_dec(v___x_1160_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1179_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = lean_nat_land(v_val_1159_, v_val_1171_);
lean_dec(v_val_1171_);
lean_dec(v_val_1159_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1175_);
v___x_1177_ = v___x_1173_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
default: 
{
lean_object* v_val_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1189_; 
v_val_1180_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1182_ = v___x_1160_;
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_val_1180_);
lean_dec(v___x_1160_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1184_ = lean_unsigned_to_nat(64u);
v___x_1185_ = l_BitVec_sub(v___x_1184_, v_val_1159_, v_val_1180_);
lean_dec(v_val_1180_);
lean_dec(v_val_1159_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1185_);
v___x_1187_ = v___x_1182_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
else
{
lean_object* v___x_1190_; 
lean_dec(v___x_1160_);
lean_dec(v_val_1159_);
v___x_1190_ = lean_box(0);
return v___x_1190_;
}
}
else
{
lean_object* v___x_1191_; 
lean_dec(v___x_1158_);
lean_dec(v_r_1157_);
lean_dec_ref(v_s_1140_);
v___x_1191_ = lean_box(0);
return v___x_1191_;
}
}
case 4:
{
lean_object* v_l_1192_; lean_object* v_r_1193_; lean_object* v___x_1194_; 
v_l_1192_ = lean_ctor_get(v_x_1141_, 0);
lean_inc(v_l_1192_);
v_r_1193_ = lean_ctor_get(v_x_1141_, 1);
lean_inc(v_r_1193_);
lean_dec_ref(v_x_1141_);
lean_inc_ref(v_s_1140_);
v___x_1194_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_s_1140_, v_l_1192_);
if (lean_obj_tag(v___x_1194_) == 1)
{
lean_object* v_val_1195_; lean_object* v___x_1196_; 
v_val_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_val_1195_);
lean_dec_ref(v___x_1194_);
v___x_1196_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_s_1140_, v_r_1193_);
if (lean_obj_tag(v___x_1196_) == 1)
{
lean_object* v_val_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1206_; 
v_val_1197_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1199_ = v___x_1196_;
v_isShared_1200_ = v_isSharedCheck_1206_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_val_1197_);
lean_dec(v___x_1196_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1206_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1201_ = lean_unsigned_to_nat(64u);
v___x_1202_ = l_BitVec_mul(v___x_1201_, v_val_1195_, v_val_1197_);
lean_dec(v_val_1197_);
lean_dec(v_val_1195_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1202_);
v___x_1204_ = v___x_1199_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
else
{
lean_object* v___x_1207_; 
lean_dec(v___x_1196_);
lean_dec(v_val_1195_);
v___x_1207_ = lean_box(0);
return v___x_1207_;
}
}
else
{
lean_object* v___x_1208_; 
lean_dec(v___x_1194_);
lean_dec(v_r_1193_);
lean_dec_ref(v_s_1140_);
v___x_1208_ = lean_box(0);
return v___x_1208_;
}
}
case 5:
{
uint8_t v_c_1209_; 
v_c_1209_ = lean_ctor_get_uint8(v_x_1141_, sizeof(void*)*2);
switch(v_c_1209_)
{
case 0:
{
lean_object* v_l_1210_; lean_object* v_r_1211_; lean_object* v___x_1212_; 
v_l_1210_ = lean_ctor_get(v_x_1141_, 0);
lean_inc(v_l_1210_);
v_r_1211_ = lean_ctor_get(v_x_1141_, 1);
lean_inc(v_r_1211_);
lean_dec_ref(v_x_1141_);
lean_inc_ref(v_s_1140_);
v___x_1212_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_s_1140_, v_l_1210_);
if (lean_obj_tag(v___x_1212_) == 1)
{
lean_object* v_val_1213_; lean_object* v___x_1214_; 
v_val_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_val_1213_);
lean_dec_ref(v___x_1212_);
v___x_1214_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_s_1140_, v_r_1211_);
if (lean_obj_tag(v___x_1214_) == 1)
{
lean_object* v_val_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_val_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_val_1215_);
lean_dec_ref(v___x_1214_);
v___x_1216_ = lean_unsigned_to_nat(64u);
v___x_1217_ = l_BitVec_slt(v___x_1216_, v_val_1213_, v_val_1215_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_eval___redArg___closed__1, &lp_orb_x2dcompiler_Pancake_eval___redArg___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_eval___redArg___closed__1);
return v___x_1218_;
}
else
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_eval___redArg___closed__2, &lp_orb_x2dcompiler_Pancake_eval___redArg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_eval___redArg___closed__2);
return v___x_1219_;
}
}
else
{
lean_object* v___x_1220_; 
lean_dec(v___x_1214_);
lean_dec(v_val_1213_);
v___x_1220_ = lean_box(0);
return v___x_1220_;
}
}
else
{
lean_object* v___x_1221_; 
lean_dec(v___x_1212_);
lean_dec(v_r_1211_);
lean_dec_ref(v_s_1140_);
v___x_1221_ = lean_box(0);
return v___x_1221_;
}
}
case 1:
{
lean_object* v_l_1222_; lean_object* v_r_1223_; lean_object* v___x_1224_; 
v_l_1222_ = lean_ctor_get(v_x_1141_, 0);
lean_inc(v_l_1222_);
v_r_1223_ = lean_ctor_get(v_x_1141_, 1);
lean_inc(v_r_1223_);
lean_dec_ref(v_x_1141_);
lean_inc_ref(v_s_1140_);
v___x_1224_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_s_1140_, v_l_1222_);
if (lean_obj_tag(v___x_1224_) == 1)
{
lean_object* v_val_1225_; lean_object* v___x_1226_; 
v_val_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_val_1225_);
lean_dec_ref(v___x_1224_);
v___x_1226_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_s_1140_, v_r_1223_);
if (lean_obj_tag(v___x_1226_) == 1)
{
lean_object* v_val_1227_; uint8_t v___x_1228_; 
v_val_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_val_1227_);
lean_dec_ref(v___x_1226_);
v___x_1228_ = lean_nat_dec_eq(v_val_1225_, v_val_1227_);
lean_dec(v_val_1227_);
lean_dec(v_val_1225_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_eval___redArg___closed__1, &lp_orb_x2dcompiler_Pancake_eval___redArg___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_eval___redArg___closed__1);
return v___x_1229_;
}
else
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_eval___redArg___closed__2, &lp_orb_x2dcompiler_Pancake_eval___redArg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_eval___redArg___closed__2);
return v___x_1230_;
}
}
else
{
lean_object* v___x_1231_; 
lean_dec(v___x_1226_);
lean_dec(v_val_1225_);
v___x_1231_ = lean_box(0);
return v___x_1231_;
}
}
else
{
lean_object* v___x_1232_; 
lean_dec(v___x_1224_);
lean_dec(v_r_1223_);
lean_dec_ref(v_s_1140_);
v___x_1232_ = lean_box(0);
return v___x_1232_;
}
}
default: 
{
lean_object* v_l_1233_; lean_object* v_r_1234_; lean_object* v___x_1235_; 
v_l_1233_ = lean_ctor_get(v_x_1141_, 0);
lean_inc(v_l_1233_);
v_r_1234_ = lean_ctor_get(v_x_1141_, 1);
lean_inc(v_r_1234_);
lean_dec_ref(v_x_1141_);
lean_inc_ref(v_s_1140_);
v___x_1235_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_s_1140_, v_l_1233_);
if (lean_obj_tag(v___x_1235_) == 1)
{
lean_object* v_val_1236_; lean_object* v___x_1237_; 
v_val_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_val_1236_);
lean_dec_ref(v___x_1235_);
v___x_1237_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_s_1140_, v_r_1234_);
if (lean_obj_tag(v___x_1237_) == 1)
{
lean_object* v_val_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v_val_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_val_1238_);
lean_dec_ref(v___x_1237_);
v___x_1239_ = lean_unsigned_to_nat(64u);
v___x_1240_ = l_BitVec_slt(v___x_1239_, v_val_1236_, v_val_1238_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_eval___redArg___closed__2, &lp_orb_x2dcompiler_Pancake_eval___redArg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_eval___redArg___closed__2);
return v___x_1241_;
}
else
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_eval___redArg___closed__1, &lp_orb_x2dcompiler_Pancake_eval___redArg___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_eval___redArg___closed__1);
return v___x_1242_;
}
}
else
{
lean_object* v___x_1243_; 
lean_dec(v___x_1237_);
lean_dec(v_val_1236_);
v___x_1243_ = lean_box(0);
return v___x_1243_;
}
}
else
{
lean_object* v___x_1244_; 
lean_dec(v___x_1235_);
lean_dec(v_r_1234_);
lean_dec_ref(v_s_1140_);
v___x_1244_ = lean_box(0);
return v___x_1244_;
}
}
}
}
case 6:
{
lean_object* v_addr_1245_; lean_object* v___x_1246_; 
v_addr_1245_ = lean_ctor_get(v_x_1141_, 0);
lean_inc(v_addr_1245_);
lean_dec_ref(v_x_1141_);
lean_inc_ref(v_s_1140_);
v___x_1246_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_s_1140_, v_addr_1245_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_dec_ref(v_s_1140_);
return v___x_1246_;
}
else
{
lean_object* v_val_1247_; lean_object* v_memory_1248_; lean_object* v_memaddrs_1249_; uint8_t v_be_1250_; lean_object* v___x_1251_; 
v_val_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_val_1247_);
lean_dec_ref(v___x_1246_);
v_memory_1248_ = lean_ctor_get(v_s_1140_, 1);
lean_inc_ref(v_memory_1248_);
v_memaddrs_1249_ = lean_ctor_get(v_s_1140_, 2);
lean_inc_ref(v_memaddrs_1249_);
v_be_1250_ = lean_ctor_get_uint8(v_s_1140_, sizeof(void*)*6);
lean_dec_ref(v_s_1140_);
v___x_1251_ = lp_orb_x2dcompiler_Pancake_memLoadByte(v_memory_1248_, v_memaddrs_1249_, v_be_1250_, v_val_1247_);
lean_dec(v_val_1247_);
if (lean_obj_tag(v___x_1251_) == 0)
{
return v___x_1251_;
}
else
{
lean_object* v_val_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1262_; 
v_val_1252_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1254_ = v___x_1251_;
v_isShared_1255_ = v_isSharedCheck_1262_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_val_1252_);
lean_dec(v___x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1262_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1256_ = lean_unsigned_to_nat(8u);
v___x_1257_ = lean_unsigned_to_nat(64u);
v___x_1258_ = l_BitVec_setWidth(v___x_1256_, v___x_1257_, v_val_1252_);
lean_dec(v_val_1252_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v___x_1258_);
v___x_1260_ = v___x_1254_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
default: 
{
lean_object* v_addr_1263_; lean_object* v___x_1264_; 
v_addr_1263_ = lean_ctor_get(v_x_1141_, 0);
lean_inc(v_addr_1263_);
lean_dec_ref(v_x_1141_);
lean_inc_ref(v_s_1140_);
v___x_1264_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_s_1140_, v_addr_1263_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_dec_ref(v_s_1140_);
return v___x_1264_;
}
else
{
lean_object* v_val_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1278_; 
v_val_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1278_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_val_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1278_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v_memory_1269_; lean_object* v_memaddrs_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v_memory_1269_ = lean_ctor_get(v_s_1140_, 1);
lean_inc_ref(v_memory_1269_);
v_memaddrs_1270_ = lean_ctor_get(v_s_1140_, 2);
lean_inc_ref(v_memaddrs_1270_);
lean_dec_ref(v_s_1140_);
lean_inc(v_val_1265_);
v___x_1271_ = lean_apply_1(v_memaddrs_1270_, v_val_1265_);
v___x_1272_ = lean_unbox(v___x_1271_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; 
lean_dec_ref(v_memory_1269_);
lean_del_object(v___x_1267_);
lean_dec(v_val_1265_);
v___x_1273_ = lean_box(0);
return v___x_1273_;
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1274_ = lean_apply_1(v_memory_1269_, v_val_1265_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1274_);
v___x_1276_ = v___x_1267_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_eval(lean_object* v_00_u03c3_1279_, lean_object* v_s_1280_, lean_object* v_x_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_s_1280_, v_x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__8_splitter___redArg(lean_object* v_x_1283_, lean_object* v_h__1_1284_, lean_object* v_h__2_1285_, lean_object* v_h__3_1286_, lean_object* v_h__4_1287_, lean_object* v_h__5_1288_, lean_object* v_h__6_1289_, lean_object* v_h__7_1290_, lean_object* v_h__8_1291_, lean_object* v_h__9_1292_, lean_object* v_h__10_1293_){
_start:
{
switch(lean_obj_tag(v_x_1283_))
{
case 0:
{
lean_object* v_w_1294_; lean_object* v___x_1295_; 
lean_dec(v_h__10_1293_);
lean_dec(v_h__9_1292_);
lean_dec(v_h__8_1291_);
lean_dec(v_h__7_1290_);
lean_dec(v_h__6_1289_);
lean_dec(v_h__5_1288_);
lean_dec(v_h__4_1287_);
lean_dec(v_h__3_1286_);
lean_dec(v_h__2_1285_);
v_w_1294_ = lean_ctor_get(v_x_1283_, 0);
lean_inc(v_w_1294_);
lean_dec_ref(v_x_1283_);
v___x_1295_ = lean_apply_1(v_h__1_1284_, v_w_1294_);
return v___x_1295_;
}
case 1:
{
lean_object* v_name_1296_; lean_object* v___x_1297_; 
lean_dec(v_h__10_1293_);
lean_dec(v_h__9_1292_);
lean_dec(v_h__8_1291_);
lean_dec(v_h__7_1290_);
lean_dec(v_h__6_1289_);
lean_dec(v_h__5_1288_);
lean_dec(v_h__4_1287_);
lean_dec(v_h__3_1286_);
lean_dec(v_h__1_1284_);
v_name_1296_ = lean_ctor_get(v_x_1283_, 0);
lean_inc_ref(v_name_1296_);
lean_dec_ref(v_x_1283_);
v___x_1297_ = lean_apply_1(v_h__2_1285_, v_name_1296_);
return v___x_1297_;
}
case 2:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_dec(v_h__10_1293_);
lean_dec(v_h__9_1292_);
lean_dec(v_h__8_1291_);
lean_dec(v_h__7_1290_);
lean_dec(v_h__6_1289_);
lean_dec(v_h__5_1288_);
lean_dec(v_h__4_1287_);
lean_dec(v_h__2_1285_);
lean_dec(v_h__1_1284_);
v___x_1298_ = lean_box(0);
v___x_1299_ = lean_apply_1(v_h__3_1286_, v___x_1298_);
return v___x_1299_;
}
case 3:
{
uint8_t v_bop_1300_; lean_object* v_l_1301_; lean_object* v_r_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec(v_h__10_1293_);
lean_dec(v_h__9_1292_);
lean_dec(v_h__8_1291_);
lean_dec(v_h__7_1290_);
lean_dec(v_h__6_1289_);
lean_dec(v_h__5_1288_);
lean_dec(v_h__3_1286_);
lean_dec(v_h__2_1285_);
lean_dec(v_h__1_1284_);
v_bop_1300_ = lean_ctor_get_uint8(v_x_1283_, sizeof(void*)*2);
v_l_1301_ = lean_ctor_get(v_x_1283_, 0);
lean_inc(v_l_1301_);
v_r_1302_ = lean_ctor_get(v_x_1283_, 1);
lean_inc(v_r_1302_);
lean_dec_ref(v_x_1283_);
v___x_1303_ = lean_box(v_bop_1300_);
v___x_1304_ = lean_apply_3(v_h__4_1287_, v___x_1303_, v_l_1301_, v_r_1302_);
return v___x_1304_;
}
case 4:
{
lean_object* v_l_1305_; lean_object* v_r_1306_; lean_object* v___x_1307_; 
lean_dec(v_h__10_1293_);
lean_dec(v_h__9_1292_);
lean_dec(v_h__8_1291_);
lean_dec(v_h__7_1290_);
lean_dec(v_h__6_1289_);
lean_dec(v_h__4_1287_);
lean_dec(v_h__3_1286_);
lean_dec(v_h__2_1285_);
lean_dec(v_h__1_1284_);
v_l_1305_ = lean_ctor_get(v_x_1283_, 0);
lean_inc(v_l_1305_);
v_r_1306_ = lean_ctor_get(v_x_1283_, 1);
lean_inc(v_r_1306_);
lean_dec_ref(v_x_1283_);
v___x_1307_ = lean_apply_2(v_h__5_1288_, v_l_1305_, v_r_1306_);
return v___x_1307_;
}
case 5:
{
uint8_t v_c_1308_; 
lean_dec(v_h__10_1293_);
lean_dec(v_h__9_1292_);
lean_dec(v_h__5_1288_);
lean_dec(v_h__4_1287_);
lean_dec(v_h__3_1286_);
lean_dec(v_h__2_1285_);
lean_dec(v_h__1_1284_);
v_c_1308_ = lean_ctor_get_uint8(v_x_1283_, sizeof(void*)*2);
switch(v_c_1308_)
{
case 0:
{
lean_object* v_l_1309_; lean_object* v_r_1310_; lean_object* v___x_1311_; 
lean_dec(v_h__8_1291_);
lean_dec(v_h__7_1290_);
v_l_1309_ = lean_ctor_get(v_x_1283_, 0);
lean_inc(v_l_1309_);
v_r_1310_ = lean_ctor_get(v_x_1283_, 1);
lean_inc(v_r_1310_);
lean_dec_ref(v_x_1283_);
v___x_1311_ = lean_apply_2(v_h__6_1289_, v_l_1309_, v_r_1310_);
return v___x_1311_;
}
case 1:
{
lean_object* v_l_1312_; lean_object* v_r_1313_; lean_object* v___x_1314_; 
lean_dec(v_h__8_1291_);
lean_dec(v_h__6_1289_);
v_l_1312_ = lean_ctor_get(v_x_1283_, 0);
lean_inc(v_l_1312_);
v_r_1313_ = lean_ctor_get(v_x_1283_, 1);
lean_inc(v_r_1313_);
lean_dec_ref(v_x_1283_);
v___x_1314_ = lean_apply_2(v_h__7_1290_, v_l_1312_, v_r_1313_);
return v___x_1314_;
}
default: 
{
lean_object* v_l_1315_; lean_object* v_r_1316_; lean_object* v___x_1317_; 
lean_dec(v_h__7_1290_);
lean_dec(v_h__6_1289_);
v_l_1315_ = lean_ctor_get(v_x_1283_, 0);
lean_inc(v_l_1315_);
v_r_1316_ = lean_ctor_get(v_x_1283_, 1);
lean_inc(v_r_1316_);
lean_dec_ref(v_x_1283_);
v___x_1317_ = lean_apply_2(v_h__8_1291_, v_l_1315_, v_r_1316_);
return v___x_1317_;
}
}
}
case 6:
{
lean_object* v_addr_1318_; lean_object* v___x_1319_; 
lean_dec(v_h__10_1293_);
lean_dec(v_h__8_1291_);
lean_dec(v_h__7_1290_);
lean_dec(v_h__6_1289_);
lean_dec(v_h__5_1288_);
lean_dec(v_h__4_1287_);
lean_dec(v_h__3_1286_);
lean_dec(v_h__2_1285_);
lean_dec(v_h__1_1284_);
v_addr_1318_ = lean_ctor_get(v_x_1283_, 0);
lean_inc(v_addr_1318_);
lean_dec_ref(v_x_1283_);
v___x_1319_ = lean_apply_1(v_h__9_1292_, v_addr_1318_);
return v___x_1319_;
}
default: 
{
lean_object* v_addr_1320_; lean_object* v___x_1321_; 
lean_dec(v_h__9_1292_);
lean_dec(v_h__8_1291_);
lean_dec(v_h__7_1290_);
lean_dec(v_h__6_1289_);
lean_dec(v_h__5_1288_);
lean_dec(v_h__4_1287_);
lean_dec(v_h__3_1286_);
lean_dec(v_h__2_1285_);
lean_dec(v_h__1_1284_);
v_addr_1320_ = lean_ctor_get(v_x_1283_, 0);
lean_inc(v_addr_1320_);
lean_dec_ref(v_x_1283_);
v___x_1321_ = lean_apply_1(v_h__10_1293_, v_addr_1320_);
return v___x_1321_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__8_splitter(lean_object* v_motive_1322_, lean_object* v_x_1323_, lean_object* v_h__1_1324_, lean_object* v_h__2_1325_, lean_object* v_h__3_1326_, lean_object* v_h__4_1327_, lean_object* v_h__5_1328_, lean_object* v_h__6_1329_, lean_object* v_h__7_1330_, lean_object* v_h__8_1331_, lean_object* v_h__9_1332_, lean_object* v_h__10_1333_){
_start:
{
switch(lean_obj_tag(v_x_1323_))
{
case 0:
{
lean_object* v_w_1334_; lean_object* v___x_1335_; 
lean_dec(v_h__10_1333_);
lean_dec(v_h__9_1332_);
lean_dec(v_h__8_1331_);
lean_dec(v_h__7_1330_);
lean_dec(v_h__6_1329_);
lean_dec(v_h__5_1328_);
lean_dec(v_h__4_1327_);
lean_dec(v_h__3_1326_);
lean_dec(v_h__2_1325_);
v_w_1334_ = lean_ctor_get(v_x_1323_, 0);
lean_inc(v_w_1334_);
lean_dec_ref(v_x_1323_);
v___x_1335_ = lean_apply_1(v_h__1_1324_, v_w_1334_);
return v___x_1335_;
}
case 1:
{
lean_object* v_name_1336_; lean_object* v___x_1337_; 
lean_dec(v_h__10_1333_);
lean_dec(v_h__9_1332_);
lean_dec(v_h__8_1331_);
lean_dec(v_h__7_1330_);
lean_dec(v_h__6_1329_);
lean_dec(v_h__5_1328_);
lean_dec(v_h__4_1327_);
lean_dec(v_h__3_1326_);
lean_dec(v_h__1_1324_);
v_name_1336_ = lean_ctor_get(v_x_1323_, 0);
lean_inc_ref(v_name_1336_);
lean_dec_ref(v_x_1323_);
v___x_1337_ = lean_apply_1(v_h__2_1325_, v_name_1336_);
return v___x_1337_;
}
case 2:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec(v_h__10_1333_);
lean_dec(v_h__9_1332_);
lean_dec(v_h__8_1331_);
lean_dec(v_h__7_1330_);
lean_dec(v_h__6_1329_);
lean_dec(v_h__5_1328_);
lean_dec(v_h__4_1327_);
lean_dec(v_h__2_1325_);
lean_dec(v_h__1_1324_);
v___x_1338_ = lean_box(0);
v___x_1339_ = lean_apply_1(v_h__3_1326_, v___x_1338_);
return v___x_1339_;
}
case 3:
{
uint8_t v_bop_1340_; lean_object* v_l_1341_; lean_object* v_r_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_dec(v_h__10_1333_);
lean_dec(v_h__9_1332_);
lean_dec(v_h__8_1331_);
lean_dec(v_h__7_1330_);
lean_dec(v_h__6_1329_);
lean_dec(v_h__5_1328_);
lean_dec(v_h__3_1326_);
lean_dec(v_h__2_1325_);
lean_dec(v_h__1_1324_);
v_bop_1340_ = lean_ctor_get_uint8(v_x_1323_, sizeof(void*)*2);
v_l_1341_ = lean_ctor_get(v_x_1323_, 0);
lean_inc(v_l_1341_);
v_r_1342_ = lean_ctor_get(v_x_1323_, 1);
lean_inc(v_r_1342_);
lean_dec_ref(v_x_1323_);
v___x_1343_ = lean_box(v_bop_1340_);
v___x_1344_ = lean_apply_3(v_h__4_1327_, v___x_1343_, v_l_1341_, v_r_1342_);
return v___x_1344_;
}
case 4:
{
lean_object* v_l_1345_; lean_object* v_r_1346_; lean_object* v___x_1347_; 
lean_dec(v_h__10_1333_);
lean_dec(v_h__9_1332_);
lean_dec(v_h__8_1331_);
lean_dec(v_h__7_1330_);
lean_dec(v_h__6_1329_);
lean_dec(v_h__4_1327_);
lean_dec(v_h__3_1326_);
lean_dec(v_h__2_1325_);
lean_dec(v_h__1_1324_);
v_l_1345_ = lean_ctor_get(v_x_1323_, 0);
lean_inc(v_l_1345_);
v_r_1346_ = lean_ctor_get(v_x_1323_, 1);
lean_inc(v_r_1346_);
lean_dec_ref(v_x_1323_);
v___x_1347_ = lean_apply_2(v_h__5_1328_, v_l_1345_, v_r_1346_);
return v___x_1347_;
}
case 5:
{
uint8_t v_c_1348_; 
lean_dec(v_h__10_1333_);
lean_dec(v_h__9_1332_);
lean_dec(v_h__5_1328_);
lean_dec(v_h__4_1327_);
lean_dec(v_h__3_1326_);
lean_dec(v_h__2_1325_);
lean_dec(v_h__1_1324_);
v_c_1348_ = lean_ctor_get_uint8(v_x_1323_, sizeof(void*)*2);
switch(v_c_1348_)
{
case 0:
{
lean_object* v_l_1349_; lean_object* v_r_1350_; lean_object* v___x_1351_; 
lean_dec(v_h__8_1331_);
lean_dec(v_h__7_1330_);
v_l_1349_ = lean_ctor_get(v_x_1323_, 0);
lean_inc(v_l_1349_);
v_r_1350_ = lean_ctor_get(v_x_1323_, 1);
lean_inc(v_r_1350_);
lean_dec_ref(v_x_1323_);
v___x_1351_ = lean_apply_2(v_h__6_1329_, v_l_1349_, v_r_1350_);
return v___x_1351_;
}
case 1:
{
lean_object* v_l_1352_; lean_object* v_r_1353_; lean_object* v___x_1354_; 
lean_dec(v_h__8_1331_);
lean_dec(v_h__6_1329_);
v_l_1352_ = lean_ctor_get(v_x_1323_, 0);
lean_inc(v_l_1352_);
v_r_1353_ = lean_ctor_get(v_x_1323_, 1);
lean_inc(v_r_1353_);
lean_dec_ref(v_x_1323_);
v___x_1354_ = lean_apply_2(v_h__7_1330_, v_l_1352_, v_r_1353_);
return v___x_1354_;
}
default: 
{
lean_object* v_l_1355_; lean_object* v_r_1356_; lean_object* v___x_1357_; 
lean_dec(v_h__7_1330_);
lean_dec(v_h__6_1329_);
v_l_1355_ = lean_ctor_get(v_x_1323_, 0);
lean_inc(v_l_1355_);
v_r_1356_ = lean_ctor_get(v_x_1323_, 1);
lean_inc(v_r_1356_);
lean_dec_ref(v_x_1323_);
v___x_1357_ = lean_apply_2(v_h__8_1331_, v_l_1355_, v_r_1356_);
return v___x_1357_;
}
}
}
case 6:
{
lean_object* v_addr_1358_; lean_object* v___x_1359_; 
lean_dec(v_h__10_1333_);
lean_dec(v_h__8_1331_);
lean_dec(v_h__7_1330_);
lean_dec(v_h__6_1329_);
lean_dec(v_h__5_1328_);
lean_dec(v_h__4_1327_);
lean_dec(v_h__3_1326_);
lean_dec(v_h__2_1325_);
lean_dec(v_h__1_1324_);
v_addr_1358_ = lean_ctor_get(v_x_1323_, 0);
lean_inc(v_addr_1358_);
lean_dec_ref(v_x_1323_);
v___x_1359_ = lean_apply_1(v_h__9_1332_, v_addr_1358_);
return v___x_1359_;
}
default: 
{
lean_object* v_addr_1360_; lean_object* v___x_1361_; 
lean_dec(v_h__9_1332_);
lean_dec(v_h__8_1331_);
lean_dec(v_h__7_1330_);
lean_dec(v_h__6_1329_);
lean_dec(v_h__5_1328_);
lean_dec(v_h__4_1327_);
lean_dec(v_h__3_1326_);
lean_dec(v_h__2_1325_);
lean_dec(v_h__1_1324_);
v_addr_1360_ = lean_ctor_get(v_x_1323_, 0);
lean_inc(v_addr_1360_);
lean_dec_ref(v_x_1323_);
v___x_1361_ = lean_apply_1(v_h__10_1333_, v_addr_1360_);
return v___x_1361_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__1_splitter___redArg(lean_object* v_x_1362_, lean_object* v_x_1363_, lean_object* v_h__1_1364_, lean_object* v_h__2_1365_){
_start:
{
if (lean_obj_tag(v_x_1362_) == 1)
{
if (lean_obj_tag(v_x_1363_) == 1)
{
lean_object* v_val_1366_; lean_object* v_val_1367_; lean_object* v___x_1368_; 
lean_dec(v_h__2_1365_);
v_val_1366_ = lean_ctor_get(v_x_1362_, 0);
lean_inc(v_val_1366_);
lean_dec_ref(v_x_1362_);
v_val_1367_ = lean_ctor_get(v_x_1363_, 0);
lean_inc(v_val_1367_);
lean_dec_ref(v_x_1363_);
v___x_1368_ = lean_apply_2(v_h__1_1364_, v_val_1366_, v_val_1367_);
return v___x_1368_;
}
else
{
lean_object* v___x_1369_; 
lean_dec(v_h__1_1364_);
v___x_1369_ = lean_apply_3(v_h__2_1365_, v_x_1362_, v_x_1363_, lean_box(0));
return v___x_1369_;
}
}
else
{
lean_object* v___x_1370_; 
lean_dec(v_h__1_1364_);
v___x_1370_ = lean_apply_3(v_h__2_1365_, v_x_1362_, v_x_1363_, lean_box(0));
return v___x_1370_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__1_splitter(lean_object* v_motive_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_, lean_object* v_h__1_1374_, lean_object* v_h__2_1375_){
_start:
{
if (lean_obj_tag(v_x_1372_) == 1)
{
if (lean_obj_tag(v_x_1373_) == 1)
{
lean_object* v_val_1376_; lean_object* v_val_1377_; lean_object* v___x_1378_; 
lean_dec(v_h__2_1375_);
v_val_1376_ = lean_ctor_get(v_x_1372_, 0);
lean_inc(v_val_1376_);
lean_dec_ref(v_x_1372_);
v_val_1377_ = lean_ctor_get(v_x_1373_, 0);
lean_inc(v_val_1377_);
lean_dec_ref(v_x_1373_);
v___x_1378_ = lean_apply_2(v_h__1_1374_, v_val_1376_, v_val_1377_);
return v___x_1378_;
}
else
{
lean_object* v___x_1379_; 
lean_dec(v_h__1_1374_);
v___x_1379_ = lean_apply_3(v_h__2_1375_, v_x_1372_, v_x_1373_, lean_box(0));
return v___x_1379_;
}
}
else
{
lean_object* v___x_1380_; 
lean_dec(v_h__1_1374_);
v___x_1380_ = lean_apply_3(v_h__2_1375_, v_x_1372_, v_x_1373_, lean_box(0));
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_instReprBinop_repr_match__1_splitter___redArg(uint8_t v_x_1381_, lean_object* v_h__1_1382_, lean_object* v_h__2_1383_, lean_object* v_h__3_1384_){
_start:
{
switch(v_x_1381_)
{
case 0:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_dec(v_h__3_1384_);
lean_dec(v_h__2_1383_);
v___x_1385_ = lean_box(0);
v___x_1386_ = lean_apply_1(v_h__1_1382_, v___x_1385_);
return v___x_1386_;
}
case 1:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_dec(v_h__3_1384_);
lean_dec(v_h__1_1382_);
v___x_1387_ = lean_box(0);
v___x_1388_ = lean_apply_1(v_h__2_1383_, v___x_1387_);
return v___x_1388_;
}
default: 
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec(v_h__2_1383_);
lean_dec(v_h__1_1382_);
v___x_1389_ = lean_box(0);
v___x_1390_ = lean_apply_1(v_h__3_1384_, v___x_1389_);
return v___x_1390_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_instReprBinop_repr_match__1_splitter___redArg___boxed(lean_object* v_x_1391_, lean_object* v_h__1_1392_, lean_object* v_h__2_1393_, lean_object* v_h__3_1394_){
_start:
{
uint8_t v_x_36__boxed_1395_; lean_object* v_res_1396_; 
v_x_36__boxed_1395_ = lean_unbox(v_x_1391_);
v_res_1396_ = lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_instReprBinop_repr_match__1_splitter___redArg(v_x_36__boxed_1395_, v_h__1_1392_, v_h__2_1393_, v_h__3_1394_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_instReprBinop_repr_match__1_splitter(lean_object* v_motive_1397_, uint8_t v_x_1398_, lean_object* v_h__1_1399_, lean_object* v_h__2_1400_, lean_object* v_h__3_1401_){
_start:
{
switch(v_x_1398_)
{
case 0:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_dec(v_h__3_1401_);
lean_dec(v_h__2_1400_);
v___x_1402_ = lean_box(0);
v___x_1403_ = lean_apply_1(v_h__1_1399_, v___x_1402_);
return v___x_1403_;
}
case 1:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec(v_h__3_1401_);
lean_dec(v_h__1_1399_);
v___x_1404_ = lean_box(0);
v___x_1405_ = lean_apply_1(v_h__2_1400_, v___x_1404_);
return v___x_1405_;
}
default: 
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec(v_h__2_1400_);
lean_dec(v_h__1_1399_);
v___x_1406_ = lean_box(0);
v___x_1407_ = lean_apply_1(v_h__3_1401_, v___x_1406_);
return v___x_1407_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_instReprBinop_repr_match__1_splitter___boxed(lean_object* v_motive_1408_, lean_object* v_x_1409_, lean_object* v_h__1_1410_, lean_object* v_h__2_1411_, lean_object* v_h__3_1412_){
_start:
{
uint8_t v_x_51__boxed_1413_; lean_object* v_res_1414_; 
v_x_51__boxed_1413_ = lean_unbox(v_x_1409_);
v_res_1414_ = lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_instReprBinop_repr_match__1_splitter(v_motive_1408_, v_x_51__boxed_1413_, v_h__1_1410_, v_h__2_1411_, v_h__3_1412_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__6_splitter___redArg(lean_object* v_x_1415_, lean_object* v_h__1_1416_, lean_object* v_h__2_1417_){
_start:
{
if (lean_obj_tag(v_x_1415_) == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_dec(v_h__1_1416_);
v___x_1418_ = lean_box(0);
v___x_1419_ = lean_apply_1(v_h__2_1417_, v___x_1418_);
return v___x_1419_;
}
else
{
lean_object* v_val_1420_; lean_object* v___x_1421_; 
lean_dec(v_h__2_1417_);
v_val_1420_ = lean_ctor_get(v_x_1415_, 0);
lean_inc(v_val_1420_);
lean_dec_ref(v_x_1415_);
v___x_1421_ = lean_apply_1(v_h__1_1416_, v_val_1420_);
return v___x_1421_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__6_splitter(lean_object* v_motive_1422_, lean_object* v_x_1423_, lean_object* v_h__1_1424_, lean_object* v_h__2_1425_){
_start:
{
if (lean_obj_tag(v_x_1423_) == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec(v_h__1_1424_);
v___x_1426_ = lean_box(0);
v___x_1427_ = lean_apply_1(v_h__2_1425_, v___x_1426_);
return v___x_1427_;
}
else
{
lean_object* v_val_1428_; lean_object* v___x_1429_; 
lean_dec(v_h__2_1425_);
v_val_1428_ = lean_ctor_get(v_x_1423_, 0);
lean_inc(v_val_1428_);
lean_dec_ref(v_x_1423_);
v___x_1429_ = lean_apply_1(v_h__1_1424_, v_val_1428_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__4_splitter___redArg(lean_object* v_x_1430_, lean_object* v_h__1_1431_, lean_object* v_h__2_1432_){
_start:
{
if (lean_obj_tag(v_x_1430_) == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec(v_h__1_1431_);
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_apply_1(v_h__2_1432_, v___x_1433_);
return v___x_1434_;
}
else
{
lean_object* v_val_1435_; lean_object* v___x_1436_; 
lean_dec(v_h__2_1432_);
v_val_1435_ = lean_ctor_get(v_x_1430_, 0);
lean_inc(v_val_1435_);
lean_dec_ref(v_x_1430_);
v___x_1436_ = lean_apply_1(v_h__1_1431_, v_val_1435_);
return v___x_1436_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_eval_match__4_splitter(lean_object* v_motive_1437_, lean_object* v_x_1438_, lean_object* v_h__1_1439_, lean_object* v_h__2_1440_){
_start:
{
if (lean_obj_tag(v_x_1438_) == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_dec(v_h__1_1439_);
v___x_1441_ = lean_box(0);
v___x_1442_ = lean_apply_1(v_h__2_1440_, v___x_1441_);
return v___x_1442_;
}
else
{
lean_object* v_val_1443_; lean_object* v___x_1444_; 
lean_dec(v_h__2_1440_);
v_val_1443_ = lean_ctor_get(v_x_1438_, 0);
lean_inc(v_val_1443_);
lean_dec_ref(v_x_1438_);
v___x_1444_ = lean_apply_1(v_h__1_1439_, v_val_1443_);
return v___x_1444_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_ctorIdx(lean_object* v_x_1445_){
_start:
{
switch(lean_obj_tag(v_x_1445_))
{
case 0:
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
return v___x_1446_;
}
case 1:
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_unsigned_to_nat(1u);
return v___x_1447_;
}
case 2:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_unsigned_to_nat(2u);
return v___x_1448_;
}
case 3:
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_unsigned_to_nat(3u);
return v___x_1449_;
}
case 4:
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_unsigned_to_nat(4u);
return v___x_1450_;
}
case 5:
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_unsigned_to_nat(5u);
return v___x_1451_;
}
case 6:
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_unsigned_to_nat(6u);
return v___x_1452_;
}
case 7:
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_unsigned_to_nat(7u);
return v___x_1453_;
}
case 8:
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_unsigned_to_nat(8u);
return v___x_1454_;
}
default: 
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_unsigned_to_nat(9u);
return v___x_1455_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_ctorIdx___boxed(lean_object* v_x_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorIdx(v_x_1456_);
lean_dec(v_x_1456_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(lean_object* v_t_1458_, lean_object* v_k_1459_){
_start:
{
switch(lean_obj_tag(v_t_1458_))
{
case 0:
{
return v_k_1459_;
}
case 1:
{
lean_object* v_v_1460_; lean_object* v_e_1461_; lean_object* v_cont_1462_; lean_object* v___x_1463_; 
v_v_1460_ = lean_ctor_get(v_t_1458_, 0);
lean_inc_ref(v_v_1460_);
v_e_1461_ = lean_ctor_get(v_t_1458_, 1);
lean_inc(v_e_1461_);
v_cont_1462_ = lean_ctor_get(v_t_1458_, 2);
lean_inc(v_cont_1462_);
lean_dec_ref(v_t_1458_);
v___x_1463_ = lean_apply_3(v_k_1459_, v_v_1460_, v_e_1461_, v_cont_1462_);
return v___x_1463_;
}
case 2:
{
lean_object* v_v_1464_; lean_object* v_e_1465_; lean_object* v___x_1466_; 
v_v_1464_ = lean_ctor_get(v_t_1458_, 0);
lean_inc_ref(v_v_1464_);
v_e_1465_ = lean_ctor_get(v_t_1458_, 1);
lean_inc(v_e_1465_);
lean_dec_ref(v_t_1458_);
v___x_1466_ = lean_apply_2(v_k_1459_, v_v_1464_, v_e_1465_);
return v___x_1466_;
}
case 4:
{
lean_object* v_name_1467_; lean_object* v_confPtr_1468_; lean_object* v_confLen_1469_; lean_object* v_arrPtr_1470_; lean_object* v_arrLen_1471_; lean_object* v___x_1472_; 
v_name_1467_ = lean_ctor_get(v_t_1458_, 0);
lean_inc_ref(v_name_1467_);
v_confPtr_1468_ = lean_ctor_get(v_t_1458_, 1);
lean_inc(v_confPtr_1468_);
v_confLen_1469_ = lean_ctor_get(v_t_1458_, 2);
lean_inc(v_confLen_1469_);
v_arrPtr_1470_ = lean_ctor_get(v_t_1458_, 3);
lean_inc(v_arrPtr_1470_);
v_arrLen_1471_ = lean_ctor_get(v_t_1458_, 4);
lean_inc(v_arrLen_1471_);
lean_dec_ref(v_t_1458_);
v___x_1472_ = lean_apply_5(v_k_1459_, v_name_1467_, v_confPtr_1468_, v_confLen_1469_, v_arrPtr_1470_, v_arrLen_1471_);
return v___x_1472_;
}
case 6:
{
lean_object* v_e_1473_; lean_object* v_c1_1474_; lean_object* v_c2_1475_; lean_object* v___x_1476_; 
v_e_1473_ = lean_ctor_get(v_t_1458_, 0);
lean_inc(v_e_1473_);
v_c1_1474_ = lean_ctor_get(v_t_1458_, 1);
lean_inc(v_c1_1474_);
v_c2_1475_ = lean_ctor_get(v_t_1458_, 2);
lean_inc(v_c2_1475_);
lean_dec_ref(v_t_1458_);
v___x_1476_ = lean_apply_3(v_k_1459_, v_e_1473_, v_c1_1474_, v_c2_1475_);
return v___x_1476_;
}
case 8:
{
lean_object* v_e_1477_; lean_object* v___x_1478_; 
v_e_1477_ = lean_ctor_get(v_t_1458_, 0);
lean_inc(v_e_1477_);
lean_dec_ref(v_t_1458_);
v___x_1478_ = lean_apply_1(v_k_1459_, v_e_1477_);
return v___x_1478_;
}
default: 
{
lean_object* v_dst_1479_; lean_object* v_src_1480_; lean_object* v___x_1481_; 
v_dst_1479_ = lean_ctor_get(v_t_1458_, 0);
lean_inc(v_dst_1479_);
v_src_1480_ = lean_ctor_get(v_t_1458_, 1);
lean_inc(v_src_1480_);
lean_dec(v_t_1458_);
v___x_1481_ = lean_apply_2(v_k_1459_, v_dst_1479_, v_src_1480_);
return v___x_1481_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim(lean_object* v_motive_1482_, lean_object* v_ctorIdx_1483_, lean_object* v_t_1484_, lean_object* v_h_1485_, lean_object* v_k_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1484_, v_k_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___boxed(lean_object* v_motive_1488_, lean_object* v_ctorIdx_1489_, lean_object* v_t_1490_, lean_object* v_h_1491_, lean_object* v_k_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim(v_motive_1488_, v_ctorIdx_1489_, v_t_1490_, v_h_1491_, v_k_1492_);
lean_dec(v_ctorIdx_1489_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_skip_elim___redArg(lean_object* v_t_1494_, lean_object* v_skip_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1494_, v_skip_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_skip_elim(lean_object* v_motive_1497_, lean_object* v_t_1498_, lean_object* v_h_1499_, lean_object* v_skip_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1498_, v_skip_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_dec_elim___redArg(lean_object* v_t_1502_, lean_object* v_dec_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1502_, v_dec_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_dec_elim(lean_object* v_motive_1505_, lean_object* v_t_1506_, lean_object* v_h_1507_, lean_object* v_dec_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1506_, v_dec_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_assign_elim___redArg(lean_object* v_t_1510_, lean_object* v_assign_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1510_, v_assign_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_assign_elim(lean_object* v_motive_1513_, lean_object* v_t_1514_, lean_object* v_h_1515_, lean_object* v_assign_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1514_, v_assign_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_store_elim___redArg(lean_object* v_t_1518_, lean_object* v_store_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1518_, v_store_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_store_elim(lean_object* v_motive_1521_, lean_object* v_t_1522_, lean_object* v_h_1523_, lean_object* v_store_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1522_, v_store_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_extCall_elim___redArg(lean_object* v_t_1526_, lean_object* v_extCall_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1526_, v_extCall_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_extCall_elim(lean_object* v_motive_1529_, lean_object* v_t_1530_, lean_object* v_h_1531_, lean_object* v_extCall_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1530_, v_extCall_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_seq_elim___redArg(lean_object* v_t_1534_, lean_object* v_seq_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1534_, v_seq_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_seq_elim(lean_object* v_motive_1537_, lean_object* v_t_1538_, lean_object* v_h_1539_, lean_object* v_seq_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1538_, v_seq_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_cond_elim___redArg(lean_object* v_t_1542_, lean_object* v_cond_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1542_, v_cond_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_cond_elim(lean_object* v_motive_1545_, lean_object* v_t_1546_, lean_object* v_h_1547_, lean_object* v_cond_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1546_, v_cond_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_while___00elim___redArg(lean_object* v_t_1550_, lean_object* v_while___1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1550_, v_while___1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_while___00elim(lean_object* v_motive_1553_, lean_object* v_t_1554_, lean_object* v_h_1555_, lean_object* v_while___1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1554_, v_while___1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_ret_elim___redArg(lean_object* v_t_1558_, lean_object* v_ret_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1558_, v_ret_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_ret_elim(lean_object* v_motive_1561_, lean_object* v_t_1562_, lean_object* v_h_1563_, lean_object* v_ret_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1562_, v_ret_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_storeByte_elim___redArg(lean_object* v_t_1566_, lean_object* v_storeByte_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1566_, v_storeByte_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeProg_storeByte_elim(lean_object* v_motive_1569_, lean_object* v_t_1570_, lean_object* v_h_1571_, lean_object* v_storeByte_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = lp_orb_x2dcompiler_Pancake_PancakeProg_ctorElim___redArg(v_t_1570_, v_storeByte_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr(lean_object* v_x_1631_, lean_object* v_prec_1632_){
_start:
{
lean_object* v___y_1634_; 
switch(lean_obj_tag(v_x_1631_))
{
case 0:
{
lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1640_ = lean_unsigned_to_nat(1024u);
v___x_1641_ = lean_nat_dec_le(v___x_1640_, v_prec_1632_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; 
v___x_1642_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1634_ = v___x_1642_;
goto v___jp_1633_;
}
else
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1634_ = v___x_1643_;
goto v___jp_1633_;
}
}
case 1:
{
lean_object* v_v_1644_; lean_object* v_e_1645_; lean_object* v_cont_1646_; lean_object* v___x_1647_; lean_object* v___y_1649_; uint8_t v___x_1665_; 
v_v_1644_ = lean_ctor_get(v_x_1631_, 0);
lean_inc_ref(v_v_1644_);
v_e_1645_ = lean_ctor_get(v_x_1631_, 1);
lean_inc(v_e_1645_);
v_cont_1646_ = lean_ctor_get(v_x_1631_, 2);
lean_inc(v_cont_1646_);
lean_dec_ref(v_x_1631_);
v___x_1647_ = lean_unsigned_to_nat(1024u);
v___x_1665_ = lean_nat_dec_le(v___x_1647_, v_prec_1632_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1649_ = v___x_1666_;
goto v___jp_1648_;
}
else
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1649_ = v___x_1667_;
goto v___jp_1648_;
}
v___jp_1648_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1650_ = lean_box(1);
v___x_1651_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__4));
v___x_1652_ = l_String_quote(v_v_1644_);
v___x_1653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1651_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v___x_1650_);
v___x_1656_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_e_1645_, v___x_1647_);
v___x_1657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_ctor_set(v___x_1658_, 1, v___x_1650_);
v___x_1659_ = lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr(v_cont_1646_, v___x_1647_);
v___x_1660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
lean_inc(v___y_1649_);
v___x_1661_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___y_1649_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = 0;
v___x_1663_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1663_, 0, v___x_1661_);
lean_ctor_set_uint8(v___x_1663_, sizeof(void*)*1, v___x_1662_);
v___x_1664_ = l_Repr_addAppParen(v___x_1663_, v_prec_1632_);
return v___x_1664_;
}
}
case 2:
{
lean_object* v_v_1668_; lean_object* v_e_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1694_; 
v_v_1668_ = lean_ctor_get(v_x_1631_, 0);
v_e_1669_ = lean_ctor_get(v_x_1631_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1671_ = v_x_1631_;
v_isShared_1672_ = v_isSharedCheck_1694_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_e_1669_);
lean_inc(v_v_1668_);
lean_dec(v_x_1631_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1694_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___y_1674_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1690_ = lean_unsigned_to_nat(1024u);
v___x_1691_ = lean_nat_dec_le(v___x_1690_, v_prec_1632_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1674_ = v___x_1692_;
goto v___jp_1673_;
}
else
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1674_ = v___x_1693_;
goto v___jp_1673_;
}
v___jp_1673_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1675_ = lean_box(1);
v___x_1676_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__7));
v___x_1677_ = l_String_quote(v_v_1668_);
v___x_1678_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set_tag(v___x_1671_, 5);
lean_ctor_set(v___x_1671_, 1, v___x_1678_);
lean_ctor_set(v___x_1671_, 0, v___x_1676_);
v___x_1680_ = v___x_1671_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v___x_1675_);
v___x_1682_ = lean_unsigned_to_nat(1024u);
v___x_1683_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_e_1669_, v___x_1682_);
v___x_1684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1681_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
lean_inc(v___y_1674_);
v___x_1685_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___y_1674_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = 0;
v___x_1687_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1687_, 0, v___x_1685_);
lean_ctor_set_uint8(v___x_1687_, sizeof(void*)*1, v___x_1686_);
v___x_1688_ = l_Repr_addAppParen(v___x_1687_, v_prec_1632_);
return v___x_1688_;
}
}
}
}
case 3:
{
lean_object* v_dst_1695_; lean_object* v_src_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1720_; 
v_dst_1695_ = lean_ctor_get(v_x_1631_, 0);
v_src_1696_ = lean_ctor_get(v_x_1631_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1698_ = v_x_1631_;
v_isShared_1699_ = v_isSharedCheck_1720_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_src_1696_);
lean_inc(v_dst_1695_);
lean_dec(v_x_1631_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1720_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___y_1701_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1716_ = lean_unsigned_to_nat(1024u);
v___x_1717_ = lean_nat_dec_le(v___x_1716_, v_prec_1632_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1701_ = v___x_1718_;
goto v___jp_1700_;
}
else
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1701_ = v___x_1719_;
goto v___jp_1700_;
}
v___jp_1700_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1702_ = lean_box(1);
v___x_1703_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__10));
v___x_1704_ = lean_unsigned_to_nat(1024u);
v___x_1705_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_dst_1695_, v___x_1704_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set_tag(v___x_1698_, 5);
lean_ctor_set(v___x_1698_, 1, v___x_1705_);
lean_ctor_set(v___x_1698_, 0, v___x_1703_);
v___x_1707_ = v___x_1698_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v___x_1702_);
v___x_1709_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_src_1696_, v___x_1704_);
v___x_1710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
lean_inc(v___y_1701_);
v___x_1711_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___y_1701_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = 0;
v___x_1713_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1713_, 0, v___x_1711_);
lean_ctor_set_uint8(v___x_1713_, sizeof(void*)*1, v___x_1712_);
v___x_1714_ = l_Repr_addAppParen(v___x_1713_, v_prec_1632_);
return v___x_1714_;
}
}
}
}
case 4:
{
lean_object* v_name_1721_; lean_object* v_confPtr_1722_; lean_object* v_confLen_1723_; lean_object* v_arrPtr_1724_; lean_object* v_arrLen_1725_; lean_object* v___y_1727_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v_name_1721_ = lean_ctor_get(v_x_1631_, 0);
lean_inc_ref(v_name_1721_);
v_confPtr_1722_ = lean_ctor_get(v_x_1631_, 1);
lean_inc(v_confPtr_1722_);
v_confLen_1723_ = lean_ctor_get(v_x_1631_, 2);
lean_inc(v_confLen_1723_);
v_arrPtr_1724_ = lean_ctor_get(v_x_1631_, 3);
lean_inc(v_arrPtr_1724_);
v_arrLen_1725_ = lean_ctor_get(v_x_1631_, 4);
lean_inc(v_arrLen_1725_);
lean_dec_ref(v_x_1631_);
v___x_1750_ = lean_unsigned_to_nat(1024u);
v___x_1751_ = lean_nat_dec_le(v___x_1750_, v_prec_1632_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1727_ = v___x_1752_;
goto v___jp_1726_;
}
else
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1727_ = v___x_1753_;
goto v___jp_1726_;
}
v___jp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1728_ = lean_box(1);
v___x_1729_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__13));
v___x_1730_ = l_String_quote(v_name_1721_);
v___x_1731_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
v___x_1732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1729_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v___x_1728_);
v___x_1734_ = lean_unsigned_to_nat(1024u);
v___x_1735_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_confPtr_1722_, v___x_1734_);
v___x_1736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1733_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
lean_ctor_set(v___x_1737_, 1, v___x_1728_);
v___x_1738_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_confLen_1723_, v___x_1734_);
v___x_1739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1737_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
lean_ctor_set(v___x_1740_, 1, v___x_1728_);
v___x_1741_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_arrPtr_1724_, v___x_1734_);
v___x_1742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1740_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v___x_1728_);
v___x_1744_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_arrLen_1725_, v___x_1734_);
v___x_1745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
lean_inc(v___y_1727_);
v___x_1746_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___y_1727_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = 0;
v___x_1748_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1748_, 0, v___x_1746_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*1, v___x_1747_);
v___x_1749_ = l_Repr_addAppParen(v___x_1748_, v_prec_1632_);
return v___x_1749_;
}
}
case 5:
{
lean_object* v_c1_1754_; lean_object* v_c2_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1778_; 
v_c1_1754_ = lean_ctor_get(v_x_1631_, 0);
v_c2_1755_ = lean_ctor_get(v_x_1631_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1757_ = v_x_1631_;
v_isShared_1758_ = v_isSharedCheck_1778_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_c2_1755_);
lean_inc(v_c1_1754_);
lean_dec(v_x_1631_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1778_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___y_1761_; uint8_t v___x_1775_; 
v___x_1759_ = lean_unsigned_to_nat(1024u);
v___x_1775_ = lean_nat_dec_le(v___x_1759_, v_prec_1632_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1761_ = v___x_1776_;
goto v___jp_1760_;
}
else
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1761_ = v___x_1777_;
goto v___jp_1760_;
}
v___jp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1762_ = lean_box(1);
v___x_1763_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__16));
v___x_1764_ = lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr(v_c1_1754_, v___x_1759_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 1, v___x_1764_);
lean_ctor_set(v___x_1757_, 0, v___x_1763_);
v___x_1766_ = v___x_1757_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1763_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v___x_1762_);
v___x_1768_ = lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr(v_c2_1755_, v___x_1759_);
v___x_1769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
lean_inc(v___y_1761_);
v___x_1770_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___y_1761_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = 0;
v___x_1772_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1772_, 0, v___x_1770_);
lean_ctor_set_uint8(v___x_1772_, sizeof(void*)*1, v___x_1771_);
v___x_1773_ = l_Repr_addAppParen(v___x_1772_, v_prec_1632_);
return v___x_1773_;
}
}
}
}
case 6:
{
lean_object* v_e_1779_; lean_object* v_c1_1780_; lean_object* v_c2_1781_; lean_object* v___x_1782_; lean_object* v___y_1784_; uint8_t v___x_1799_; 
v_e_1779_ = lean_ctor_get(v_x_1631_, 0);
lean_inc(v_e_1779_);
v_c1_1780_ = lean_ctor_get(v_x_1631_, 1);
lean_inc(v_c1_1780_);
v_c2_1781_ = lean_ctor_get(v_x_1631_, 2);
lean_inc(v_c2_1781_);
lean_dec_ref(v_x_1631_);
v___x_1782_ = lean_unsigned_to_nat(1024u);
v___x_1799_ = lean_nat_dec_le(v___x_1782_, v_prec_1632_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; 
v___x_1800_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1784_ = v___x_1800_;
goto v___jp_1783_;
}
else
{
lean_object* v___x_1801_; 
v___x_1801_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1784_ = v___x_1801_;
goto v___jp_1783_;
}
v___jp_1783_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1785_ = lean_box(1);
v___x_1786_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__19));
v___x_1787_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_e_1779_, v___x_1782_);
v___x_1788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
lean_ctor_set(v___x_1789_, 1, v___x_1785_);
v___x_1790_ = lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr(v_c1_1780_, v___x_1782_);
v___x_1791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
lean_ctor_set(v___x_1792_, 1, v___x_1785_);
v___x_1793_ = lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr(v_c2_1781_, v___x_1782_);
v___x_1794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1792_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
lean_inc(v___y_1784_);
v___x_1795_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___y_1784_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
v___x_1796_ = 0;
v___x_1797_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1797_, 0, v___x_1795_);
lean_ctor_set_uint8(v___x_1797_, sizeof(void*)*1, v___x_1796_);
v___x_1798_ = l_Repr_addAppParen(v___x_1797_, v_prec_1632_);
return v___x_1798_;
}
}
case 7:
{
lean_object* v_e_1802_; lean_object* v_c_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1826_; 
v_e_1802_ = lean_ctor_get(v_x_1631_, 0);
v_c_1803_ = lean_ctor_get(v_x_1631_, 1);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1805_ = v_x_1631_;
v_isShared_1806_ = v_isSharedCheck_1826_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_c_1803_);
lean_inc(v_e_1802_);
lean_dec(v_x_1631_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1826_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v___y_1809_; uint8_t v___x_1823_; 
v___x_1807_ = lean_unsigned_to_nat(1024u);
v___x_1823_ = lean_nat_dec_le(v___x_1807_, v_prec_1632_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1809_ = v___x_1824_;
goto v___jp_1808_;
}
else
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1809_ = v___x_1825_;
goto v___jp_1808_;
}
v___jp_1808_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1810_ = lean_box(1);
v___x_1811_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__22));
v___x_1812_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_e_1802_, v___x_1807_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set_tag(v___x_1805_, 5);
lean_ctor_set(v___x_1805_, 1, v___x_1812_);
lean_ctor_set(v___x_1805_, 0, v___x_1811_);
v___x_1814_ = v___x_1805_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v___x_1810_);
v___x_1816_ = lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr(v_c_1803_, v___x_1807_);
v___x_1817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
lean_inc(v___y_1809_);
v___x_1818_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___y_1809_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = 0;
v___x_1820_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1820_, 0, v___x_1818_);
lean_ctor_set_uint8(v___x_1820_, sizeof(void*)*1, v___x_1819_);
v___x_1821_ = l_Repr_addAppParen(v___x_1820_, v_prec_1632_);
return v___x_1821_;
}
}
}
}
case 8:
{
lean_object* v_e_1827_; lean_object* v___y_1829_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v_e_1827_ = lean_ctor_get(v_x_1631_, 0);
lean_inc(v_e_1827_);
lean_dec_ref(v_x_1631_);
v___x_1838_ = lean_unsigned_to_nat(1024u);
v___x_1839_ = lean_nat_dec_le(v___x_1838_, v_prec_1632_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1829_ = v___x_1840_;
goto v___jp_1828_;
}
else
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1829_ = v___x_1841_;
goto v___jp_1828_;
}
v___jp_1828_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1830_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__25));
v___x_1831_ = lean_unsigned_to_nat(1024u);
v___x_1832_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_e_1827_, v___x_1831_);
v___x_1833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1830_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
lean_inc(v___y_1829_);
v___x_1834_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___y_1829_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = 0;
v___x_1836_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set_uint8(v___x_1836_, sizeof(void*)*1, v___x_1835_);
v___x_1837_ = l_Repr_addAppParen(v___x_1836_, v_prec_1632_);
return v___x_1837_;
}
}
default: 
{
lean_object* v_dst_1842_; lean_object* v_src_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1867_; 
v_dst_1842_ = lean_ctor_get(v_x_1631_, 0);
v_src_1843_ = lean_ctor_get(v_x_1631_, 1);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1845_ = v_x_1631_;
v_isShared_1846_ = v_isSharedCheck_1867_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_src_1843_);
lean_inc(v_dst_1842_);
lean_dec(v_x_1631_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1867_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___y_1848_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1863_ = lean_unsigned_to_nat(1024u);
v___x_1864_ = lean_nat_dec_le(v___x_1863_, v_prec_1632_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__8);
v___y_1848_ = v___x_1865_;
goto v___jp_1847_;
}
else
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9, &lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_instReprResult_repr___closed__9);
v___y_1848_ = v___x_1866_;
goto v___jp_1847_;
}
v___jp_1847_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1849_ = lean_box(1);
v___x_1850_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__28));
v___x_1851_ = lean_unsigned_to_nat(1024u);
v___x_1852_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_dst_1842_, v___x_1851_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set_tag(v___x_1845_, 5);
lean_ctor_set(v___x_1845_, 1, v___x_1852_);
lean_ctor_set(v___x_1845_, 0, v___x_1850_);
v___x_1854_ = v___x_1845_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
lean_ctor_set(v___x_1855_, 1, v___x_1849_);
v___x_1856_ = lp_orb_x2dcompiler_Pancake_instReprPancakeExp_repr(v_src_1843_, v___x_1851_);
v___x_1857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
lean_inc(v___y_1848_);
v___x_1858_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___y_1848_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = 0;
v___x_1860_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*1, v___x_1859_);
v___x_1861_ = l_Repr_addAppParen(v___x_1860_, v_prec_1632_);
return v___x_1861_;
}
}
}
}
}
v___jp_1633_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1635_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___closed__1));
lean_inc(v___y_1634_);
v___x_1636_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___y_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = 0;
v___x_1638_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set_uint8(v___x_1638_, sizeof(void*)*1, v___x_1637_);
v___x_1639_ = l_Repr_addAppParen(v___x_1638_, v_prec_1632_);
return v___x_1639_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr___boxed(lean_object* v_x_1868_, lean_object* v_prec_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = lp_orb_x2dcompiler_Pancake_instReprPancakeProg_repr(v_x_1868_, v_prec_1869_);
lean_dec(v_prec_1869_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_setLocal(lean_object* v_lc_1873_, lean_object* v_v_1874_, lean_object* v_val_1875_, lean_object* v_k_1876_){
_start:
{
uint8_t v___x_1877_; 
v___x_1877_ = lean_string_dec_eq(v_k_1876_, v_v_1874_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; 
lean_dec(v_val_1875_);
v___x_1878_ = lean_apply_1(v_lc_1873_, v_k_1876_);
return v___x_1878_;
}
else
{
lean_object* v___x_1879_; 
lean_dec_ref(v_k_1876_);
lean_dec_ref(v_lc_1873_);
v___x_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1879_, 0, v_val_1875_);
return v___x_1879_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_setLocal___boxed(lean_object* v_lc_1880_, lean_object* v_v_1881_, lean_object* v_val_1882_, lean_object* v_k_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = lp_orb_x2dcompiler_Pancake_setLocal(v_lc_1880_, v_v_1881_, v_val_1882_, v_k_1883_);
lean_dec_ref(v_v_1881_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_resVar(lean_object* v_lc_1885_, lean_object* v_v_1886_, lean_object* v_old_1887_, lean_object* v_k_1888_){
_start:
{
uint8_t v___x_1889_; 
v___x_1889_ = lean_string_dec_eq(v_k_1888_, v_v_1886_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_apply_1(v_lc_1885_, v_k_1888_);
return v___x_1890_;
}
else
{
lean_dec_ref(v_k_1888_);
lean_dec_ref(v_lc_1885_);
lean_inc(v_old_1887_);
return v_old_1887_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_resVar___boxed(lean_object* v_lc_1891_, lean_object* v_v_1892_, lean_object* v_old_1893_, lean_object* v_k_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = lp_orb_x2dcompiler_Pancake_resVar(v_lc_1891_, v_v_1892_, v_old_1893_, v_k_1894_);
lean_dec(v_old_1893_);
lean_dec_ref(v_v_1892_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_emptyLocals___redArg___lam__0(lean_object* v_x_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = lean_box(0);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_emptyLocals___redArg___lam__0___boxed(lean_object* v_x_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = lp_orb_x2dcompiler_Pancake_emptyLocals___redArg___lam__0(v_x_1898_);
lean_dec_ref(v_x_1898_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_emptyLocals___redArg(lean_object* v_s_1901_){
_start:
{
lean_object* v_memory_1902_; lean_object* v_memaddrs_1903_; uint8_t v_be_1904_; lean_object* v_clock_1905_; lean_object* v_ffi_1906_; lean_object* v_baseAddr_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1915_; 
v_memory_1902_ = lean_ctor_get(v_s_1901_, 1);
v_memaddrs_1903_ = lean_ctor_get(v_s_1901_, 2);
v_be_1904_ = lean_ctor_get_uint8(v_s_1901_, sizeof(void*)*6);
v_clock_1905_ = lean_ctor_get(v_s_1901_, 3);
v_ffi_1906_ = lean_ctor_get(v_s_1901_, 4);
v_baseAddr_1907_ = lean_ctor_get(v_s_1901_, 5);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_s_1901_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v_s_1901_, 0);
lean_dec(v_unused_1916_);
v___x_1909_ = v_s_1901_;
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_baseAddr_1907_);
lean_inc(v_ffi_1906_);
lean_inc(v_clock_1905_);
lean_inc(v_memaddrs_1903_);
lean_inc(v_memory_1902_);
lean_dec(v_s_1901_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___f_1911_; lean_object* v___x_1913_; 
v___f_1911_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_emptyLocals___redArg___closed__0));
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___f_1911_);
v___x_1913_ = v___x_1909_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___f_1911_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_memory_1902_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_memaddrs_1903_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_clock_1905_);
lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_ffi_1906_);
lean_ctor_set(v_reuseFailAlloc_1914_, 5, v_baseAddr_1907_);
lean_ctor_set_uint8(v_reuseFailAlloc_1914_, sizeof(void*)*6, v_be_1904_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_emptyLocals(lean_object* v_00_u03c3_1917_, lean_object* v_s_1918_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = lp_orb_x2dcompiler_Pancake_emptyLocals___redArg(v_s_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_decClock___redArg(lean_object* v_s_1920_){
_start:
{
lean_object* v_locals_1921_; lean_object* v_memory_1922_; lean_object* v_memaddrs_1923_; uint8_t v_be_1924_; lean_object* v_clock_1925_; lean_object* v_ffi_1926_; lean_object* v_baseAddr_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1936_; 
v_locals_1921_ = lean_ctor_get(v_s_1920_, 0);
v_memory_1922_ = lean_ctor_get(v_s_1920_, 1);
v_memaddrs_1923_ = lean_ctor_get(v_s_1920_, 2);
v_be_1924_ = lean_ctor_get_uint8(v_s_1920_, sizeof(void*)*6);
v_clock_1925_ = lean_ctor_get(v_s_1920_, 3);
v_ffi_1926_ = lean_ctor_get(v_s_1920_, 4);
v_baseAddr_1927_ = lean_ctor_get(v_s_1920_, 5);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_s_1920_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1929_ = v_s_1920_;
v_isShared_1930_ = v_isSharedCheck_1936_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_baseAddr_1927_);
lean_inc(v_ffi_1926_);
lean_inc(v_clock_1925_);
lean_inc(v_memaddrs_1923_);
lean_inc(v_memory_1922_);
lean_inc(v_locals_1921_);
lean_dec(v_s_1920_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1936_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1931_ = lean_unsigned_to_nat(1u);
v___x_1932_ = lean_nat_sub(v_clock_1925_, v___x_1931_);
lean_dec(v_clock_1925_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 3, v___x_1932_);
v___x_1934_ = v___x_1929_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_locals_1921_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_memory_1922_);
lean_ctor_set(v_reuseFailAlloc_1935_, 2, v_memaddrs_1923_);
lean_ctor_set(v_reuseFailAlloc_1935_, 3, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1935_, 4, v_ffi_1926_);
lean_ctor_set(v_reuseFailAlloc_1935_, 5, v_baseAddr_1927_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*6, v_be_1924_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_decClock(lean_object* v_00_u03c3_1937_, lean_object* v_s_1938_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = lp_orb_x2dcompiler_Pancake_decClock___redArg(v_s_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_clampClock___redArg(lean_object* v_old_1940_, lean_object* v_r_1941_){
_start:
{
lean_object* v_snd_1942_; lean_object* v_fst_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1967_; 
v_snd_1942_ = lean_ctor_get(v_r_1941_, 1);
v_fst_1943_ = lean_ctor_get(v_r_1941_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_r_1941_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1945_ = v_r_1941_;
v_isShared_1946_ = v_isSharedCheck_1967_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_snd_1942_);
lean_inc(v_fst_1943_);
lean_dec(v_r_1941_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1967_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v_locals_1947_; lean_object* v_memory_1948_; lean_object* v_memaddrs_1949_; uint8_t v_be_1950_; lean_object* v_clock_1951_; lean_object* v_ffi_1952_; lean_object* v_baseAddr_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1966_; 
v_locals_1947_ = lean_ctor_get(v_snd_1942_, 0);
v_memory_1948_ = lean_ctor_get(v_snd_1942_, 1);
v_memaddrs_1949_ = lean_ctor_get(v_snd_1942_, 2);
v_be_1950_ = lean_ctor_get_uint8(v_snd_1942_, sizeof(void*)*6);
v_clock_1951_ = lean_ctor_get(v_snd_1942_, 3);
v_ffi_1952_ = lean_ctor_get(v_snd_1942_, 4);
v_baseAddr_1953_ = lean_ctor_get(v_snd_1942_, 5);
v_isSharedCheck_1966_ = !lean_is_exclusive(v_snd_1942_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1955_ = v_snd_1942_;
v_isShared_1956_ = v_isSharedCheck_1966_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_baseAddr_1953_);
lean_inc(v_ffi_1952_);
lean_inc(v_clock_1951_);
lean_inc(v_memaddrs_1949_);
lean_inc(v_memory_1948_);
lean_inc(v_locals_1947_);
lean_dec(v_snd_1942_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1966_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___y_1958_; uint8_t v___x_1965_; 
v___x_1965_ = lean_nat_dec_le(v_old_1940_, v_clock_1951_);
if (v___x_1965_ == 0)
{
lean_dec(v_old_1940_);
v___y_1958_ = v_clock_1951_;
goto v___jp_1957_;
}
else
{
lean_dec(v_clock_1951_);
v___y_1958_ = v_old_1940_;
goto v___jp_1957_;
}
v___jp_1957_:
{
lean_object* v___x_1960_; 
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 3, v___y_1958_);
v___x_1960_ = v___x_1955_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_locals_1947_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_memory_1948_);
lean_ctor_set(v_reuseFailAlloc_1964_, 2, v_memaddrs_1949_);
lean_ctor_set(v_reuseFailAlloc_1964_, 3, v___y_1958_);
lean_ctor_set(v_reuseFailAlloc_1964_, 4, v_ffi_1952_);
lean_ctor_set(v_reuseFailAlloc_1964_, 5, v_baseAddr_1953_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*6, v_be_1950_);
v___x_1960_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1962_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v___x_1960_);
v___x_1962_ = v___x_1945_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_fst_1943_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_clampClock(lean_object* v_00_u03c3_1968_, lean_object* v_old_1969_, lean_object* v_r_1970_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = lp_orb_x2dcompiler_Pancake_clampClock___redArg(v_old_1969_, v_r_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeSem___redArg(lean_object* v_oracle_1976_, lean_object* v_x_1977_, lean_object* v_x_1978_){
_start:
{
switch(lean_obj_tag(v_x_1977_))
{
case 0:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
lean_dec_ref(v_oracle_1976_);
v___x_1991_ = lean_box(0);
v___x_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
lean_ctor_set(v___x_1992_, 1, v_x_1978_);
return v___x_1992_;
}
case 1:
{
lean_object* v_v_1993_; lean_object* v_e_1994_; lean_object* v_cont_1995_; lean_object* v___x_1996_; 
v_v_1993_ = lean_ctor_get(v_x_1977_, 0);
lean_inc_ref(v_v_1993_);
v_e_1994_ = lean_ctor_get(v_x_1977_, 1);
lean_inc(v_e_1994_);
v_cont_1995_ = lean_ctor_get(v_x_1977_, 2);
lean_inc(v_cont_1995_);
lean_dec_ref(v_x_1977_);
lean_inc_ref(v_x_1978_);
v___x_1996_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_x_1978_, v_e_1994_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
lean_dec(v_cont_1995_);
lean_dec_ref(v_v_1993_);
lean_dec_ref(v_oracle_1976_);
v___x_1997_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__0));
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
lean_ctor_set(v___x_1998_, 1, v_x_1978_);
return v___x_1998_;
}
else
{
lean_object* v_val_1999_; lean_object* v_locals_2000_; lean_object* v_memory_2001_; lean_object* v_memaddrs_2002_; uint8_t v_be_2003_; lean_object* v_clock_2004_; lean_object* v_ffi_2005_; lean_object* v_baseAddr_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2040_; 
v_val_1999_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_val_1999_);
lean_dec_ref(v___x_1996_);
v_locals_2000_ = lean_ctor_get(v_x_1978_, 0);
v_memory_2001_ = lean_ctor_get(v_x_1978_, 1);
v_memaddrs_2002_ = lean_ctor_get(v_x_1978_, 2);
v_be_2003_ = lean_ctor_get_uint8(v_x_1978_, sizeof(void*)*6);
v_clock_2004_ = lean_ctor_get(v_x_1978_, 3);
v_ffi_2005_ = lean_ctor_get(v_x_1978_, 4);
v_baseAddr_2006_ = lean_ctor_get(v_x_1978_, 5);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_x_1978_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2008_ = v_x_1978_;
v_isShared_2009_ = v_isSharedCheck_2040_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_baseAddr_2006_);
lean_inc(v_ffi_2005_);
lean_inc(v_clock_2004_);
lean_inc(v_memaddrs_2002_);
lean_inc(v_memory_2001_);
lean_inc(v_locals_2000_);
lean_dec(v_x_1978_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2040_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
lean_inc_ref(v_v_1993_);
lean_inc_ref(v_locals_2000_);
v___x_2010_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_setLocal___boxed), 4, 3);
lean_closure_set(v___x_2010_, 0, v_locals_2000_);
lean_closure_set(v___x_2010_, 1, v_v_1993_);
lean_closure_set(v___x_2010_, 2, v_val_1999_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v___x_2010_);
v___x_2012_ = v___x_2008_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_memory_2001_);
lean_ctor_set(v_reuseFailAlloc_2039_, 2, v_memaddrs_2002_);
lean_ctor_set(v_reuseFailAlloc_2039_, 3, v_clock_2004_);
lean_ctor_set(v_reuseFailAlloc_2039_, 4, v_ffi_2005_);
lean_ctor_set(v_reuseFailAlloc_2039_, 5, v_baseAddr_2006_);
lean_ctor_set_uint8(v_reuseFailAlloc_2039_, sizeof(void*)*6, v_be_2003_);
v___x_2012_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v_r_2013_; lean_object* v_snd_2014_; lean_object* v_fst_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2038_; 
v_r_2013_ = lp_orb_x2dcompiler_Pancake_PancakeSem___redArg(v_oracle_1976_, v_cont_1995_, v___x_2012_);
v_snd_2014_ = lean_ctor_get(v_r_2013_, 1);
v_fst_2015_ = lean_ctor_get(v_r_2013_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_r_2013_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2017_ = v_r_2013_;
v_isShared_2018_ = v_isSharedCheck_2038_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_snd_2014_);
lean_inc(v_fst_2015_);
lean_dec(v_r_2013_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2038_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v_locals_2019_; lean_object* v_memory_2020_; lean_object* v_memaddrs_2021_; uint8_t v_be_2022_; lean_object* v_clock_2023_; lean_object* v_ffi_2024_; lean_object* v_baseAddr_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2037_; 
v_locals_2019_ = lean_ctor_get(v_snd_2014_, 0);
v_memory_2020_ = lean_ctor_get(v_snd_2014_, 1);
v_memaddrs_2021_ = lean_ctor_get(v_snd_2014_, 2);
v_be_2022_ = lean_ctor_get_uint8(v_snd_2014_, sizeof(void*)*6);
v_clock_2023_ = lean_ctor_get(v_snd_2014_, 3);
v_ffi_2024_ = lean_ctor_get(v_snd_2014_, 4);
v_baseAddr_2025_ = lean_ctor_get(v_snd_2014_, 5);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_snd_2014_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2027_ = v_snd_2014_;
v_isShared_2028_ = v_isSharedCheck_2037_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_baseAddr_2025_);
lean_inc(v_ffi_2024_);
lean_inc(v_clock_2023_);
lean_inc(v_memaddrs_2021_);
lean_inc(v_memory_2020_);
lean_inc(v_locals_2019_);
lean_dec(v_snd_2014_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2037_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
lean_inc_ref(v_v_1993_);
v___x_2029_ = lean_apply_1(v_locals_2000_, v_v_1993_);
v___x_2030_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_resVar___boxed), 4, 3);
lean_closure_set(v___x_2030_, 0, v_locals_2019_);
lean_closure_set(v___x_2030_, 1, v_v_1993_);
lean_closure_set(v___x_2030_, 2, v___x_2029_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2030_);
v___x_2032_ = v___x_2027_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2030_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_memory_2020_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v_memaddrs_2021_);
lean_ctor_set(v_reuseFailAlloc_2036_, 3, v_clock_2023_);
lean_ctor_set(v_reuseFailAlloc_2036_, 4, v_ffi_2024_);
lean_ctor_set(v_reuseFailAlloc_2036_, 5, v_baseAddr_2025_);
lean_ctor_set_uint8(v_reuseFailAlloc_2036_, sizeof(void*)*6, v_be_2022_);
v___x_2032_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2034_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 1, v___x_2032_);
v___x_2034_ = v___x_2017_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_fst_2015_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
}
}
}
case 2:
{
lean_object* v_v_2041_; lean_object* v_e_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref(v_oracle_1976_);
v_v_2041_ = lean_ctor_get(v_x_1977_, 0);
v_e_2042_ = lean_ctor_get(v_x_1977_, 1);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2044_ = v_x_1977_;
v_isShared_2045_ = v_isSharedCheck_2071_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_e_2042_);
lean_inc(v_v_2041_);
lean_dec(v_x_1977_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2071_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; 
lean_inc_ref(v_x_1978_);
v___x_2046_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_x_1978_, v_e_2042_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
lean_dec_ref(v_v_2041_);
v___x_2047_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__0));
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 0);
lean_ctor_set(v___x_2044_, 1, v_x_1978_);
lean_ctor_set(v___x_2044_, 0, v___x_2047_);
v___x_2049_ = v___x_2044_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_x_1978_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
else
{
lean_object* v_val_2051_; lean_object* v_locals_2052_; lean_object* v_memory_2053_; lean_object* v_memaddrs_2054_; uint8_t v_be_2055_; lean_object* v_clock_2056_; lean_object* v_ffi_2057_; lean_object* v_baseAddr_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2070_; 
v_val_2051_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_val_2051_);
lean_dec_ref(v___x_2046_);
v_locals_2052_ = lean_ctor_get(v_x_1978_, 0);
v_memory_2053_ = lean_ctor_get(v_x_1978_, 1);
v_memaddrs_2054_ = lean_ctor_get(v_x_1978_, 2);
v_be_2055_ = lean_ctor_get_uint8(v_x_1978_, sizeof(void*)*6);
v_clock_2056_ = lean_ctor_get(v_x_1978_, 3);
v_ffi_2057_ = lean_ctor_get(v_x_1978_, 4);
v_baseAddr_2058_ = lean_ctor_get(v_x_1978_, 5);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_x_1978_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2060_ = v_x_1978_;
v_isShared_2061_ = v_isSharedCheck_2070_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_baseAddr_2058_);
lean_inc(v_ffi_2057_);
lean_inc(v_clock_2056_);
lean_inc(v_memaddrs_2054_);
lean_inc(v_memory_2053_);
lean_inc(v_locals_2052_);
lean_dec(v_x_1978_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2070_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2062_ = lean_box(0);
v___x_2063_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_setLocal___boxed), 4, 3);
lean_closure_set(v___x_2063_, 0, v_locals_2052_);
lean_closure_set(v___x_2063_, 1, v_v_2041_);
lean_closure_set(v___x_2063_, 2, v_val_2051_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2063_);
v___x_2065_ = v___x_2060_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_memory_2053_);
lean_ctor_set(v_reuseFailAlloc_2069_, 2, v_memaddrs_2054_);
lean_ctor_set(v_reuseFailAlloc_2069_, 3, v_clock_2056_);
lean_ctor_set(v_reuseFailAlloc_2069_, 4, v_ffi_2057_);
lean_ctor_set(v_reuseFailAlloc_2069_, 5, v_baseAddr_2058_);
lean_ctor_set_uint8(v_reuseFailAlloc_2069_, sizeof(void*)*6, v_be_2055_);
v___x_2065_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2067_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 0);
lean_ctor_set(v___x_2044_, 1, v___x_2065_);
lean_ctor_set(v___x_2044_, 0, v___x_2062_);
v___x_2067_ = v___x_2044_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
}
case 3:
{
lean_object* v_dst_2072_; lean_object* v_src_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2111_; 
lean_dec_ref(v_oracle_1976_);
v_dst_2072_ = lean_ctor_get(v_x_1977_, 0);
v_src_2073_ = lean_ctor_get(v_x_1977_, 1);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2075_ = v_x_1977_;
v_isShared_2076_ = v_isSharedCheck_2111_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_src_2073_);
lean_inc(v_dst_2072_);
lean_dec(v_x_1977_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2111_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; 
lean_inc_ref(v_x_1978_);
v___x_2077_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_x_1978_, v_dst_2072_);
if (lean_obj_tag(v___x_2077_) == 1)
{
lean_object* v_val_2078_; lean_object* v___x_2079_; 
v_val_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_val_2078_);
lean_dec_ref(v___x_2077_);
lean_inc_ref(v_x_1978_);
v___x_2079_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_x_1978_, v_src_2073_);
if (lean_obj_tag(v___x_2079_) == 1)
{
lean_object* v_val_2080_; lean_object* v_locals_2081_; lean_object* v_memory_2082_; lean_object* v_memaddrs_2083_; uint8_t v_be_2084_; lean_object* v_clock_2085_; lean_object* v_ffi_2086_; lean_object* v_baseAddr_2087_; lean_object* v___x_2088_; 
v_val_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_val_2080_);
lean_dec_ref(v___x_2079_);
v_locals_2081_ = lean_ctor_get(v_x_1978_, 0);
v_memory_2082_ = lean_ctor_get(v_x_1978_, 1);
v_memaddrs_2083_ = lean_ctor_get(v_x_1978_, 2);
v_be_2084_ = lean_ctor_get_uint8(v_x_1978_, sizeof(void*)*6);
v_clock_2085_ = lean_ctor_get(v_x_1978_, 3);
v_ffi_2086_ = lean_ctor_get(v_x_1978_, 4);
v_baseAddr_2087_ = lean_ctor_get(v_x_1978_, 5);
lean_inc_ref(v_memaddrs_2083_);
lean_inc_ref(v_memory_2082_);
v___x_2088_ = lp_orb_x2dcompiler_Pancake_memStoreWord(v_memory_2082_, v_memaddrs_2083_, v_val_2078_, v_val_2080_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__0));
if (v_isShared_2076_ == 0)
{
lean_ctor_set_tag(v___x_2075_, 0);
lean_ctor_set(v___x_2075_, 1, v_x_1978_);
lean_ctor_set(v___x_2075_, 0, v___x_2089_);
v___x_2091_ = v___x_2075_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_x_1978_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
else
{
lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2104_; 
lean_inc(v_baseAddr_2087_);
lean_inc(v_ffi_2086_);
lean_inc(v_clock_2085_);
lean_inc_ref(v_memaddrs_2083_);
lean_inc_ref(v_locals_2081_);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_x_1978_);
if (v_isSharedCheck_2104_ == 0)
{
lean_object* v_unused_2105_; lean_object* v_unused_2106_; lean_object* v_unused_2107_; lean_object* v_unused_2108_; lean_object* v_unused_2109_; lean_object* v_unused_2110_; 
v_unused_2105_ = lean_ctor_get(v_x_1978_, 5);
lean_dec(v_unused_2105_);
v_unused_2106_ = lean_ctor_get(v_x_1978_, 4);
lean_dec(v_unused_2106_);
v_unused_2107_ = lean_ctor_get(v_x_1978_, 3);
lean_dec(v_unused_2107_);
v_unused_2108_ = lean_ctor_get(v_x_1978_, 2);
lean_dec(v_unused_2108_);
v_unused_2109_ = lean_ctor_get(v_x_1978_, 1);
lean_dec(v_unused_2109_);
v_unused_2110_ = lean_ctor_get(v_x_1978_, 0);
lean_dec(v_unused_2110_);
v___x_2094_ = v_x_1978_;
v_isShared_2095_ = v_isSharedCheck_2104_;
goto v_resetjp_2093_;
}
else
{
lean_dec(v_x_1978_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2104_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_val_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v_val_2096_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_val_2096_);
lean_dec_ref(v___x_2088_);
v___x_2097_ = lean_box(0);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 1, v_val_2096_);
v___x_2099_ = v___x_2094_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_locals_2081_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_val_2096_);
lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_memaddrs_2083_);
lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_clock_2085_);
lean_ctor_set(v_reuseFailAlloc_2103_, 4, v_ffi_2086_);
lean_ctor_set(v_reuseFailAlloc_2103_, 5, v_baseAddr_2087_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*6, v_be_2084_);
v___x_2099_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2101_; 
if (v_isShared_2076_ == 0)
{
lean_ctor_set_tag(v___x_2075_, 0);
lean_ctor_set(v___x_2075_, 1, v___x_2099_);
lean_ctor_set(v___x_2075_, 0, v___x_2097_);
v___x_2101_ = v___x_2075_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
else
{
lean_dec(v___x_2079_);
lean_dec(v_val_2078_);
lean_del_object(v___x_2075_);
goto v___jp_1985_;
}
}
else
{
lean_dec(v___x_2077_);
lean_del_object(v___x_2075_);
lean_dec(v_src_2073_);
goto v___jp_1985_;
}
}
}
case 4:
{
lean_object* v_name_2112_; lean_object* v_confPtr_2113_; lean_object* v_confLen_2114_; lean_object* v_arrPtr_2115_; lean_object* v_arrLen_2116_; lean_object* v___x_2117_; 
v_name_2112_ = lean_ctor_get(v_x_1977_, 0);
lean_inc_ref(v_name_2112_);
v_confPtr_2113_ = lean_ctor_get(v_x_1977_, 1);
lean_inc(v_confPtr_2113_);
v_confLen_2114_ = lean_ctor_get(v_x_1977_, 2);
lean_inc(v_confLen_2114_);
v_arrPtr_2115_ = lean_ctor_get(v_x_1977_, 3);
lean_inc(v_arrPtr_2115_);
v_arrLen_2116_ = lean_ctor_get(v_x_1977_, 4);
lean_inc(v_arrLen_2116_);
lean_dec_ref(v_x_1977_);
lean_inc_ref(v_x_1978_);
v___x_2117_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_x_1978_, v_confPtr_2113_);
if (lean_obj_tag(v___x_2117_) == 1)
{
lean_object* v_val_2118_; lean_object* v___x_2119_; 
v_val_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_val_2118_);
lean_dec_ref(v___x_2117_);
lean_inc_ref(v_x_1978_);
v___x_2119_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_x_1978_, v_confLen_2114_);
if (lean_obj_tag(v___x_2119_) == 1)
{
lean_object* v_val_2120_; lean_object* v___x_2121_; 
v_val_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_val_2120_);
lean_dec_ref(v___x_2119_);
lean_inc_ref(v_x_1978_);
v___x_2121_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_x_1978_, v_arrPtr_2115_);
if (lean_obj_tag(v___x_2121_) == 1)
{
lean_object* v_val_2122_; lean_object* v___x_2123_; 
v_val_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_val_2122_);
lean_dec_ref(v___x_2121_);
lean_inc_ref(v_x_1978_);
v___x_2123_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_x_1978_, v_arrLen_2116_);
if (lean_obj_tag(v___x_2123_) == 1)
{
lean_object* v_val_2124_; lean_object* v_locals_2125_; lean_object* v_memory_2126_; lean_object* v_memaddrs_2127_; uint8_t v_be_2128_; lean_object* v_clock_2129_; lean_object* v_ffi_2130_; lean_object* v_baseAddr_2131_; lean_object* v___x_2132_; 
v_val_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_val_2124_);
lean_dec_ref(v___x_2123_);
v_locals_2125_ = lean_ctor_get(v_x_1978_, 0);
v_memory_2126_ = lean_ctor_get(v_x_1978_, 1);
v_memaddrs_2127_ = lean_ctor_get(v_x_1978_, 2);
v_be_2128_ = lean_ctor_get_uint8(v_x_1978_, sizeof(void*)*6);
v_clock_2129_ = lean_ctor_get(v_x_1978_, 3);
v_ffi_2130_ = lean_ctor_get(v_x_1978_, 4);
v_baseAddr_2131_ = lean_ctor_get(v_x_1978_, 5);
lean_inc_ref(v_memaddrs_2127_);
lean_inc_ref(v_memory_2126_);
v___x_2132_ = lp_orb_x2dcompiler_Pancake_readByteArray(v_memory_2126_, v_memaddrs_2127_, v_be_2128_, v_val_2118_, v_val_2120_);
lean_dec(v_val_2120_);
lean_dec(v_val_2118_);
if (lean_obj_tag(v___x_2132_) == 1)
{
lean_object* v_val_2133_; lean_object* v___x_2134_; 
v_val_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_val_2133_);
lean_dec_ref(v___x_2132_);
lean_inc_ref(v_memaddrs_2127_);
lean_inc_ref(v_memory_2126_);
v___x_2134_ = lp_orb_x2dcompiler_Pancake_readByteArray(v_memory_2126_, v_memaddrs_2127_, v_be_2128_, v_val_2122_, v_val_2124_);
lean_dec(v_val_2124_);
if (lean_obj_tag(v___x_2134_) == 1)
{
lean_object* v_val_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2178_; 
v_val_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2178_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_val_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2178_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; 
lean_inc(v_ffi_2130_);
v___x_2139_ = lean_apply_4(v_oracle_1976_, v_ffi_2130_, v_name_2112_, v_val_2133_, v_val_2135_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_outcome_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v_val_2122_);
v_outcome_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2152_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_outcome_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2152_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set_tag(v___x_2142_, 5);
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_outcome_2140_);
v___x_2145_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2147_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2145_);
v___x_2147_ = v___x_2137_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = lp_orb_x2dcompiler_Pancake_emptyLocals___redArg(v_x_1978_);
v___x_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2147_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
return v___x_2149_;
}
}
}
}
else
{
lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2171_; 
lean_inc(v_baseAddr_2131_);
lean_inc(v_clock_2129_);
lean_inc_ref(v_memaddrs_2127_);
lean_inc_ref(v_memory_2126_);
lean_inc_ref(v_locals_2125_);
lean_del_object(v___x_2137_);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_x_1978_);
if (v_isSharedCheck_2171_ == 0)
{
lean_object* v_unused_2172_; lean_object* v_unused_2173_; lean_object* v_unused_2174_; lean_object* v_unused_2175_; lean_object* v_unused_2176_; lean_object* v_unused_2177_; 
v_unused_2172_ = lean_ctor_get(v_x_1978_, 5);
lean_dec(v_unused_2172_);
v_unused_2173_ = lean_ctor_get(v_x_1978_, 4);
lean_dec(v_unused_2173_);
v_unused_2174_ = lean_ctor_get(v_x_1978_, 3);
lean_dec(v_unused_2174_);
v_unused_2175_ = lean_ctor_get(v_x_1978_, 2);
lean_dec(v_unused_2175_);
v_unused_2176_ = lean_ctor_get(v_x_1978_, 1);
lean_dec(v_unused_2176_);
v_unused_2177_ = lean_ctor_get(v_x_1978_, 0);
lean_dec(v_unused_2177_);
v___x_2154_ = v_x_1978_;
v_isShared_2155_ = v_isSharedCheck_2171_;
goto v_resetjp_2153_;
}
else
{
lean_dec(v_x_1978_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2171_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v_newState_2156_; lean_object* v_newBytes_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2170_; 
v_newState_2156_ = lean_ctor_get(v___x_2139_, 0);
v_newBytes_2157_ = lean_ctor_get(v___x_2139_, 1);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2159_ = v___x_2139_;
v_isShared_2160_ = v_isSharedCheck_2170_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_newBytes_2157_);
lean_inc(v_newState_2156_);
lean_dec(v___x_2139_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2170_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2165_; 
v___x_2161_ = lean_box(0);
v___x_2162_ = lean_box(v_be_2128_);
lean_inc_ref(v_memaddrs_2127_);
v___x_2163_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_writeByteArray___boxed), 6, 5);
lean_closure_set(v___x_2163_, 0, v_memaddrs_2127_);
lean_closure_set(v___x_2163_, 1, v___x_2162_);
lean_closure_set(v___x_2163_, 2, v_val_2122_);
lean_closure_set(v___x_2163_, 3, v_newBytes_2157_);
lean_closure_set(v___x_2163_, 4, v_memory_2126_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 4, v_newState_2156_);
lean_ctor_set(v___x_2154_, 1, v___x_2163_);
v___x_2165_ = v___x_2154_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_locals_2125_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2169_, 2, v_memaddrs_2127_);
lean_ctor_set(v_reuseFailAlloc_2169_, 3, v_clock_2129_);
lean_ctor_set(v_reuseFailAlloc_2169_, 4, v_newState_2156_);
lean_ctor_set(v_reuseFailAlloc_2169_, 5, v_baseAddr_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2169_, sizeof(void*)*6, v_be_2128_);
v___x_2165_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_object* v___x_2167_; 
if (v_isShared_2160_ == 0)
{
lean_ctor_set_tag(v___x_2159_, 0);
lean_ctor_set(v___x_2159_, 1, v___x_2165_);
lean_ctor_set(v___x_2159_, 0, v___x_2161_);
v___x_2167_ = v___x_2159_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2134_);
lean_dec(v_val_2133_);
lean_dec(v_val_2122_);
lean_dec_ref(v_name_2112_);
lean_dec_ref(v_oracle_1976_);
goto v___jp_1979_;
}
}
else
{
lean_dec(v___x_2132_);
lean_dec(v_val_2124_);
lean_dec(v_val_2122_);
lean_dec_ref(v_name_2112_);
lean_dec_ref(v_oracle_1976_);
goto v___jp_1979_;
}
}
else
{
lean_dec(v___x_2123_);
lean_dec(v_val_2122_);
lean_dec(v_val_2120_);
lean_dec(v_val_2118_);
lean_dec_ref(v_name_2112_);
lean_dec_ref(v_oracle_1976_);
goto v___jp_1982_;
}
}
else
{
lean_dec(v___x_2121_);
lean_dec(v_val_2120_);
lean_dec(v_val_2118_);
lean_dec(v_arrLen_2116_);
lean_dec_ref(v_name_2112_);
lean_dec_ref(v_oracle_1976_);
goto v___jp_1982_;
}
}
else
{
lean_dec(v___x_2119_);
lean_dec(v_val_2118_);
lean_dec(v_arrLen_2116_);
lean_dec(v_arrPtr_2115_);
lean_dec_ref(v_name_2112_);
lean_dec_ref(v_oracle_1976_);
goto v___jp_1982_;
}
}
else
{
lean_dec(v___x_2117_);
lean_dec(v_arrLen_2116_);
lean_dec(v_arrPtr_2115_);
lean_dec(v_confLen_2114_);
lean_dec_ref(v_name_2112_);
lean_dec_ref(v_oracle_1976_);
goto v___jp_1982_;
}
}
case 5:
{
lean_object* v_c1_2179_; lean_object* v_c2_2180_; lean_object* v_clock_2181_; lean_object* v___x_2182_; lean_object* v_r_2183_; lean_object* v_fst_2184_; 
v_c1_2179_ = lean_ctor_get(v_x_1977_, 0);
lean_inc(v_c1_2179_);
v_c2_2180_ = lean_ctor_get(v_x_1977_, 1);
lean_inc(v_c2_2180_);
lean_dec_ref(v_x_1977_);
v_clock_2181_ = lean_ctor_get(v_x_1978_, 3);
lean_inc(v_clock_2181_);
lean_inc_ref(v_oracle_1976_);
v___x_2182_ = lp_orb_x2dcompiler_Pancake_PancakeSem___redArg(v_oracle_1976_, v_c1_2179_, v_x_1978_);
v_r_2183_ = lp_orb_x2dcompiler_Pancake_clampClock___redArg(v_clock_2181_, v___x_2182_);
v_fst_2184_ = lean_ctor_get(v_r_2183_, 0);
lean_inc(v_fst_2184_);
if (lean_obj_tag(v_fst_2184_) == 0)
{
lean_object* v_snd_2185_; 
v_snd_2185_ = lean_ctor_get(v_r_2183_, 1);
lean_inc(v_snd_2185_);
lean_dec_ref(v_r_2183_);
v_x_1977_ = v_c2_2180_;
v_x_1978_ = v_snd_2185_;
goto _start;
}
else
{
lean_object* v_snd_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_c2_2180_);
lean_dec_ref(v_oracle_1976_);
v_snd_2187_ = lean_ctor_get(v_r_2183_, 1);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_r_2183_);
if (v_isSharedCheck_2194_ == 0)
{
lean_object* v_unused_2195_; 
v_unused_2195_ = lean_ctor_get(v_r_2183_, 0);
lean_dec(v_unused_2195_);
v___x_2189_ = v_r_2183_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_snd_2187_);
lean_dec(v_r_2183_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_fst_2184_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_snd_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
case 6:
{
lean_object* v_e_2196_; lean_object* v_c1_2197_; lean_object* v_c2_2198_; lean_object* v___x_2199_; 
v_e_2196_ = lean_ctor_get(v_x_1977_, 0);
lean_inc(v_e_2196_);
v_c1_2197_ = lean_ctor_get(v_x_1977_, 1);
lean_inc(v_c1_2197_);
v_c2_2198_ = lean_ctor_get(v_x_1977_, 2);
lean_inc(v_c2_2198_);
lean_dec_ref(v_x_1977_);
lean_inc_ref(v_x_1978_);
v___x_2199_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_x_1978_, v_e_2196_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_dec(v_c2_2198_);
lean_dec(v_c1_2197_);
lean_dec_ref(v_oracle_1976_);
v___x_2200_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__0));
v___x_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
lean_ctor_set(v___x_2201_, 1, v_x_1978_);
return v___x_2201_;
}
else
{
lean_object* v_val_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v_val_2202_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_val_2202_);
lean_dec_ref(v___x_2199_);
v___x_2203_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_eval___redArg___closed__0, &lp_orb_x2dcompiler_Pancake_eval___redArg___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_eval___redArg___closed__0);
v___x_2204_ = lean_nat_dec_eq(v_val_2202_, v___x_2203_);
lean_dec(v_val_2202_);
if (v___x_2204_ == 0)
{
lean_dec(v_c2_2198_);
v_x_1977_ = v_c1_2197_;
goto _start;
}
else
{
lean_dec(v_c1_2197_);
v_x_1977_ = v_c2_2198_;
goto _start;
}
}
}
case 7:
{
lean_object* v_e_2207_; lean_object* v_c_2208_; lean_object* v___x_2209_; 
v_e_2207_ = lean_ctor_get(v_x_1977_, 0);
v_c_2208_ = lean_ctor_get(v_x_1977_, 1);
lean_inc(v_e_2207_);
lean_inc_ref(v_x_1978_);
v___x_2209_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_x_1978_, v_e_2207_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v_oracle_1976_);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2217_ == 0)
{
lean_object* v_unused_2218_; lean_object* v_unused_2219_; 
v_unused_2218_ = lean_ctor_get(v_x_1977_, 1);
lean_dec(v_unused_2218_);
v_unused_2219_ = lean_ctor_get(v_x_1977_, 0);
lean_dec(v_unused_2219_);
v___x_2211_ = v_x_1977_;
v_isShared_2212_ = v_isSharedCheck_2217_;
goto v_resetjp_2210_;
}
else
{
lean_dec(v_x_1977_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2217_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2213_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__0));
if (v_isShared_2212_ == 0)
{
lean_ctor_set_tag(v___x_2211_, 0);
lean_ctor_set(v___x_2211_, 1, v_x_1978_);
lean_ctor_set(v___x_2211_, 0, v___x_2213_);
v___x_2215_ = v___x_2211_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_x_1978_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
else
{
lean_object* v_val_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; 
v_val_2220_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_val_2220_);
lean_dec_ref(v___x_2209_);
v___x_2221_ = lean_unsigned_to_nat(0u);
v___x_2222_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_eval___redArg___closed__0, &lp_orb_x2dcompiler_Pancake_eval___redArg___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_eval___redArg___closed__0);
v___x_2223_ = lean_nat_dec_eq(v_val_2220_, v___x_2222_);
lean_dec(v_val_2220_);
if (v___x_2223_ == 0)
{
lean_object* v_clock_2224_; uint8_t v___x_2225_; 
v_clock_2224_ = lean_ctor_get(v_x_1978_, 3);
v___x_2225_ = lean_nat_dec_eq(v_clock_2224_, v___x_2221_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v_r_2230_; lean_object* v_fst_2234_; 
v___x_2226_ = lean_unsigned_to_nat(1u);
v___x_2227_ = lean_nat_sub(v_clock_2224_, v___x_2226_);
v___x_2228_ = lp_orb_x2dcompiler_Pancake_decClock___redArg(v_x_1978_);
lean_inc(v_c_2208_);
lean_inc_ref(v_oracle_1976_);
v___x_2229_ = lp_orb_x2dcompiler_Pancake_PancakeSem___redArg(v_oracle_1976_, v_c_2208_, v___x_2228_);
v_r_2230_ = lp_orb_x2dcompiler_Pancake_clampClock___redArg(v___x_2227_, v___x_2229_);
v_fst_2234_ = lean_ctor_get(v_r_2230_, 0);
lean_inc(v_fst_2234_);
if (lean_obj_tag(v_fst_2234_) == 0)
{
goto v___jp_2231_;
}
else
{
lean_object* v_val_2235_; 
v_val_2235_ = lean_ctor_get(v_fst_2234_, 0);
switch(lean_obj_tag(v_val_2235_))
{
case 3:
{
lean_dec_ref(v_fst_2234_);
goto v___jp_2231_;
}
case 2:
{
lean_object* v_snd_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2244_; 
lean_dec_ref(v_fst_2234_);
lean_dec_ref(v_x_1977_);
lean_dec_ref(v_oracle_1976_);
v_snd_2236_ = lean_ctor_get(v_r_2230_, 1);
v_isSharedCheck_2244_ = !lean_is_exclusive(v_r_2230_);
if (v_isSharedCheck_2244_ == 0)
{
lean_object* v_unused_2245_; 
v_unused_2245_ = lean_ctor_get(v_r_2230_, 0);
lean_dec(v_unused_2245_);
v___x_2238_ = v_r_2230_;
v_isShared_2239_ = v_isSharedCheck_2244_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_snd_2236_);
lean_dec(v_r_2230_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2244_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2240_ = lean_box(0);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2240_);
v___x_2242_ = v___x_2238_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_snd_2236_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
default: 
{
lean_object* v_snd_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec_ref(v_x_1977_);
lean_dec_ref(v_oracle_1976_);
v_snd_2246_ = lean_ctor_get(v_r_2230_, 1);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_r_2230_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; 
v_unused_2254_ = lean_ctor_get(v_r_2230_, 0);
lean_dec(v_unused_2254_);
v___x_2248_ = v_r_2230_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_snd_2246_);
lean_dec(v_r_2230_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_fst_2234_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_snd_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
v___jp_2231_:
{
lean_object* v_snd_2232_; 
v_snd_2232_ = lean_ctor_get(v_r_2230_, 1);
lean_inc(v_snd_2232_);
lean_dec_ref(v_r_2230_);
v_x_1978_ = v_snd_2232_;
goto _start;
}
}
else
{
lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2263_; 
lean_dec_ref(v_oracle_1976_);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2263_ == 0)
{
lean_object* v_unused_2264_; lean_object* v_unused_2265_; 
v_unused_2264_ = lean_ctor_get(v_x_1977_, 1);
lean_dec(v_unused_2264_);
v_unused_2265_ = lean_ctor_get(v_x_1977_, 0);
lean_dec(v_unused_2265_);
v___x_2256_ = v_x_1977_;
v_isShared_2257_ = v_isSharedCheck_2263_;
goto v_resetjp_2255_;
}
else
{
lean_dec(v_x_1977_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2263_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2258_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__1));
v___x_2259_ = lp_orb_x2dcompiler_Pancake_emptyLocals___redArg(v_x_1978_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set_tag(v___x_2256_, 0);
lean_ctor_set(v___x_2256_, 1, v___x_2259_);
lean_ctor_set(v___x_2256_, 0, v___x_2258_);
v___x_2261_ = v___x_2256_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
else
{
lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2273_; 
lean_dec_ref(v_oracle_1976_);
v_isSharedCheck_2273_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2273_ == 0)
{
lean_object* v_unused_2274_; lean_object* v_unused_2275_; 
v_unused_2274_ = lean_ctor_get(v_x_1977_, 1);
lean_dec(v_unused_2274_);
v_unused_2275_ = lean_ctor_get(v_x_1977_, 0);
lean_dec(v_unused_2275_);
v___x_2267_ = v_x_1977_;
v_isShared_2268_ = v_isSharedCheck_2273_;
goto v_resetjp_2266_;
}
else
{
lean_dec(v_x_1977_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2273_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2269_ = lean_box(0);
if (v_isShared_2268_ == 0)
{
lean_ctor_set_tag(v___x_2267_, 0);
lean_ctor_set(v___x_2267_, 1, v_x_1978_);
lean_ctor_set(v___x_2267_, 0, v___x_2269_);
v___x_2271_ = v___x_2267_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v_x_1978_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
case 8:
{
lean_object* v_e_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2296_; 
lean_dec_ref(v_oracle_1976_);
v_e_2276_ = lean_ctor_get(v_x_1977_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2278_ = v_x_1977_;
v_isShared_2279_ = v_isSharedCheck_2296_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_e_2276_);
lean_dec(v_x_1977_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2296_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; 
lean_inc_ref(v_x_1978_);
v___x_2280_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_x_1978_, v_e_2276_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
lean_del_object(v___x_2278_);
v___x_2281_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__0));
v___x_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v_x_1978_);
return v___x_2282_;
}
else
{
lean_object* v_val_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2295_; 
v_val_2283_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2285_ = v___x_2280_;
v_isShared_2286_ = v_isSharedCheck_2295_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_val_2283_);
lean_dec(v___x_2280_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2295_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2279_ == 0)
{
lean_ctor_set_tag(v___x_2278_, 4);
lean_ctor_set(v___x_2278_, 0, v_val_2283_);
v___x_2288_ = v___x_2278_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_val_2283_);
v___x_2288_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2290_; 
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2288_);
v___x_2290_ = v___x_2285_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lp_orb_x2dcompiler_Pancake_emptyLocals___redArg(v_x_1978_);
v___x_2292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2290_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
return v___x_2292_;
}
}
}
}
}
}
default: 
{
lean_object* v_dst_2297_; lean_object* v_src_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_oracle_1976_);
v_dst_2297_ = lean_ctor_get(v_x_1977_, 0);
v_src_2298_ = lean_ctor_get(v_x_1977_, 1);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2300_ = v_x_1977_;
v_isShared_2301_ = v_isSharedCheck_2339_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_src_2298_);
lean_inc(v_dst_2297_);
lean_dec(v_x_1977_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2339_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; 
lean_inc_ref(v_x_1978_);
v___x_2302_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_x_1978_, v_dst_2297_);
if (lean_obj_tag(v___x_2302_) == 1)
{
lean_object* v_val_2303_; lean_object* v___x_2304_; 
v_val_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_val_2303_);
lean_dec_ref(v___x_2302_);
lean_inc_ref(v_x_1978_);
v___x_2304_ = lp_orb_x2dcompiler_Pancake_eval___redArg(v_x_1978_, v_src_2298_);
if (lean_obj_tag(v___x_2304_) == 1)
{
lean_object* v_val_2305_; lean_object* v_locals_2306_; lean_object* v_memory_2307_; lean_object* v_memaddrs_2308_; uint8_t v_be_2309_; lean_object* v_clock_2310_; lean_object* v_ffi_2311_; lean_object* v_baseAddr_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v_val_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_val_2305_);
lean_dec_ref(v___x_2304_);
v_locals_2306_ = lean_ctor_get(v_x_1978_, 0);
v_memory_2307_ = lean_ctor_get(v_x_1978_, 1);
v_memaddrs_2308_ = lean_ctor_get(v_x_1978_, 2);
v_be_2309_ = lean_ctor_get_uint8(v_x_1978_, sizeof(void*)*6);
v_clock_2310_ = lean_ctor_get(v_x_1978_, 3);
v_ffi_2311_ = lean_ctor_get(v_x_1978_, 4);
v_baseAddr_2312_ = lean_ctor_get(v_x_1978_, 5);
v___x_2313_ = lean_unsigned_to_nat(64u);
v___x_2314_ = lean_unsigned_to_nat(8u);
v___x_2315_ = l_BitVec_setWidth(v___x_2313_, v___x_2314_, v_val_2305_);
lean_dec(v_val_2305_);
lean_inc_ref(v_memaddrs_2308_);
lean_inc_ref(v_memory_2307_);
v___x_2316_ = lp_orb_x2dcompiler_Pancake_memStoreByte(v_memory_2307_, v_memaddrs_2308_, v_be_2309_, v_val_2303_, v___x_2315_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2317_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__0));
if (v_isShared_2301_ == 0)
{
lean_ctor_set_tag(v___x_2300_, 0);
lean_ctor_set(v___x_2300_, 1, v_x_1978_);
lean_ctor_set(v___x_2300_, 0, v___x_2317_);
v___x_2319_ = v___x_2300_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_x_1978_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
else
{
lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2332_; 
lean_inc(v_baseAddr_2312_);
lean_inc(v_ffi_2311_);
lean_inc(v_clock_2310_);
lean_inc_ref(v_memaddrs_2308_);
lean_inc_ref(v_locals_2306_);
v_isSharedCheck_2332_ = !lean_is_exclusive(v_x_1978_);
if (v_isSharedCheck_2332_ == 0)
{
lean_object* v_unused_2333_; lean_object* v_unused_2334_; lean_object* v_unused_2335_; lean_object* v_unused_2336_; lean_object* v_unused_2337_; lean_object* v_unused_2338_; 
v_unused_2333_ = lean_ctor_get(v_x_1978_, 5);
lean_dec(v_unused_2333_);
v_unused_2334_ = lean_ctor_get(v_x_1978_, 4);
lean_dec(v_unused_2334_);
v_unused_2335_ = lean_ctor_get(v_x_1978_, 3);
lean_dec(v_unused_2335_);
v_unused_2336_ = lean_ctor_get(v_x_1978_, 2);
lean_dec(v_unused_2336_);
v_unused_2337_ = lean_ctor_get(v_x_1978_, 1);
lean_dec(v_unused_2337_);
v_unused_2338_ = lean_ctor_get(v_x_1978_, 0);
lean_dec(v_unused_2338_);
v___x_2322_ = v_x_1978_;
v_isShared_2323_ = v_isSharedCheck_2332_;
goto v_resetjp_2321_;
}
else
{
lean_dec(v_x_1978_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2332_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v_val_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
v_val_2324_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_val_2324_);
lean_dec_ref(v___x_2316_);
v___x_2325_ = lean_box(0);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 1, v_val_2324_);
v___x_2327_ = v___x_2322_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_locals_2306_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v_val_2324_);
lean_ctor_set(v_reuseFailAlloc_2331_, 2, v_memaddrs_2308_);
lean_ctor_set(v_reuseFailAlloc_2331_, 3, v_clock_2310_);
lean_ctor_set(v_reuseFailAlloc_2331_, 4, v_ffi_2311_);
lean_ctor_set(v_reuseFailAlloc_2331_, 5, v_baseAddr_2312_);
lean_ctor_set_uint8(v_reuseFailAlloc_2331_, sizeof(void*)*6, v_be_2309_);
v___x_2327_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2329_; 
if (v_isShared_2301_ == 0)
{
lean_ctor_set_tag(v___x_2300_, 0);
lean_ctor_set(v___x_2300_, 1, v___x_2327_);
lean_ctor_set(v___x_2300_, 0, v___x_2325_);
v___x_2329_ = v___x_2300_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2325_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
else
{
lean_dec(v___x_2304_);
lean_dec(v_val_2303_);
lean_del_object(v___x_2300_);
goto v___jp_1988_;
}
}
else
{
lean_dec(v___x_2302_);
lean_del_object(v___x_2300_);
lean_dec(v_src_2298_);
goto v___jp_1988_;
}
}
}
}
v___jp_1979_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__0));
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v_x_1978_);
return v___x_1981_;
}
v___jp_1982_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__0));
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
lean_ctor_set(v___x_1984_, 1, v_x_1978_);
return v___x_1984_;
}
v___jp_1985_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__0));
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
lean_ctor_set(v___x_1987_, 1, v_x_1978_);
return v___x_1987_;
}
v___jp_1988_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PancakeSem___redArg___closed__0));
v___x_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v_x_1978_);
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PancakeSem(lean_object* v_00_u03c3_2340_, lean_object* v_oracle_2341_, lean_object* v_x_2342_, lean_object* v_x_2343_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = lp_orb_x2dcompiler_Pancake_PancakeSem___redArg(v_oracle_2341_, v_x_2342_, v_x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__12_splitter___redArg(lean_object* v_x_2345_, lean_object* v_x_2346_, lean_object* v_h__1_2347_, lean_object* v_h__2_2348_, lean_object* v_h__3_2349_, lean_object* v_h__4_2350_, lean_object* v_h__5_2351_, lean_object* v_h__6_2352_, lean_object* v_h__7_2353_, lean_object* v_h__8_2354_, lean_object* v_h__9_2355_, lean_object* v_h__10_2356_){
_start:
{
switch(lean_obj_tag(v_x_2345_))
{
case 0:
{
lean_object* v___x_2357_; 
lean_dec(v_h__10_2356_);
lean_dec(v_h__9_2355_);
lean_dec(v_h__8_2354_);
lean_dec(v_h__7_2353_);
lean_dec(v_h__6_2352_);
lean_dec(v_h__5_2351_);
lean_dec(v_h__4_2350_);
lean_dec(v_h__3_2349_);
lean_dec(v_h__2_2348_);
v___x_2357_ = lean_apply_1(v_h__1_2347_, v_x_2346_);
return v___x_2357_;
}
case 1:
{
lean_object* v_v_2358_; lean_object* v_e_2359_; lean_object* v_cont_2360_; lean_object* v___x_2361_; 
lean_dec(v_h__10_2356_);
lean_dec(v_h__9_2355_);
lean_dec(v_h__8_2354_);
lean_dec(v_h__7_2353_);
lean_dec(v_h__6_2352_);
lean_dec(v_h__5_2351_);
lean_dec(v_h__4_2350_);
lean_dec(v_h__3_2349_);
lean_dec(v_h__1_2347_);
v_v_2358_ = lean_ctor_get(v_x_2345_, 0);
lean_inc_ref(v_v_2358_);
v_e_2359_ = lean_ctor_get(v_x_2345_, 1);
lean_inc(v_e_2359_);
v_cont_2360_ = lean_ctor_get(v_x_2345_, 2);
lean_inc(v_cont_2360_);
lean_dec_ref(v_x_2345_);
v___x_2361_ = lean_apply_4(v_h__2_2348_, v_v_2358_, v_e_2359_, v_cont_2360_, v_x_2346_);
return v___x_2361_;
}
case 2:
{
lean_object* v_v_2362_; lean_object* v_e_2363_; lean_object* v___x_2364_; 
lean_dec(v_h__10_2356_);
lean_dec(v_h__9_2355_);
lean_dec(v_h__8_2354_);
lean_dec(v_h__7_2353_);
lean_dec(v_h__6_2352_);
lean_dec(v_h__5_2351_);
lean_dec(v_h__4_2350_);
lean_dec(v_h__2_2348_);
lean_dec(v_h__1_2347_);
v_v_2362_ = lean_ctor_get(v_x_2345_, 0);
lean_inc_ref(v_v_2362_);
v_e_2363_ = lean_ctor_get(v_x_2345_, 1);
lean_inc(v_e_2363_);
lean_dec_ref(v_x_2345_);
v___x_2364_ = lean_apply_3(v_h__3_2349_, v_v_2362_, v_e_2363_, v_x_2346_);
return v___x_2364_;
}
case 3:
{
lean_object* v_dst_2365_; lean_object* v_src_2366_; lean_object* v___x_2367_; 
lean_dec(v_h__10_2356_);
lean_dec(v_h__9_2355_);
lean_dec(v_h__8_2354_);
lean_dec(v_h__7_2353_);
lean_dec(v_h__6_2352_);
lean_dec(v_h__5_2351_);
lean_dec(v_h__3_2349_);
lean_dec(v_h__2_2348_);
lean_dec(v_h__1_2347_);
v_dst_2365_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_dst_2365_);
v_src_2366_ = lean_ctor_get(v_x_2345_, 1);
lean_inc(v_src_2366_);
lean_dec_ref(v_x_2345_);
v___x_2367_ = lean_apply_3(v_h__4_2350_, v_dst_2365_, v_src_2366_, v_x_2346_);
return v___x_2367_;
}
case 4:
{
lean_object* v_name_2368_; lean_object* v_confPtr_2369_; lean_object* v_confLen_2370_; lean_object* v_arrPtr_2371_; lean_object* v_arrLen_2372_; lean_object* v___x_2373_; 
lean_dec(v_h__10_2356_);
lean_dec(v_h__9_2355_);
lean_dec(v_h__8_2354_);
lean_dec(v_h__7_2353_);
lean_dec(v_h__6_2352_);
lean_dec(v_h__4_2350_);
lean_dec(v_h__3_2349_);
lean_dec(v_h__2_2348_);
lean_dec(v_h__1_2347_);
v_name_2368_ = lean_ctor_get(v_x_2345_, 0);
lean_inc_ref(v_name_2368_);
v_confPtr_2369_ = lean_ctor_get(v_x_2345_, 1);
lean_inc(v_confPtr_2369_);
v_confLen_2370_ = lean_ctor_get(v_x_2345_, 2);
lean_inc(v_confLen_2370_);
v_arrPtr_2371_ = lean_ctor_get(v_x_2345_, 3);
lean_inc(v_arrPtr_2371_);
v_arrLen_2372_ = lean_ctor_get(v_x_2345_, 4);
lean_inc(v_arrLen_2372_);
lean_dec_ref(v_x_2345_);
v___x_2373_ = lean_apply_6(v_h__5_2351_, v_name_2368_, v_confPtr_2369_, v_confLen_2370_, v_arrPtr_2371_, v_arrLen_2372_, v_x_2346_);
return v___x_2373_;
}
case 5:
{
lean_object* v_c1_2374_; lean_object* v_c2_2375_; lean_object* v___x_2376_; 
lean_dec(v_h__10_2356_);
lean_dec(v_h__9_2355_);
lean_dec(v_h__8_2354_);
lean_dec(v_h__7_2353_);
lean_dec(v_h__5_2351_);
lean_dec(v_h__4_2350_);
lean_dec(v_h__3_2349_);
lean_dec(v_h__2_2348_);
lean_dec(v_h__1_2347_);
v_c1_2374_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_c1_2374_);
v_c2_2375_ = lean_ctor_get(v_x_2345_, 1);
lean_inc(v_c2_2375_);
lean_dec_ref(v_x_2345_);
v___x_2376_ = lean_apply_3(v_h__6_2352_, v_c1_2374_, v_c2_2375_, v_x_2346_);
return v___x_2376_;
}
case 6:
{
lean_object* v_e_2377_; lean_object* v_c1_2378_; lean_object* v_c2_2379_; lean_object* v___x_2380_; 
lean_dec(v_h__10_2356_);
lean_dec(v_h__9_2355_);
lean_dec(v_h__8_2354_);
lean_dec(v_h__6_2352_);
lean_dec(v_h__5_2351_);
lean_dec(v_h__4_2350_);
lean_dec(v_h__3_2349_);
lean_dec(v_h__2_2348_);
lean_dec(v_h__1_2347_);
v_e_2377_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_e_2377_);
v_c1_2378_ = lean_ctor_get(v_x_2345_, 1);
lean_inc(v_c1_2378_);
v_c2_2379_ = lean_ctor_get(v_x_2345_, 2);
lean_inc(v_c2_2379_);
lean_dec_ref(v_x_2345_);
v___x_2380_ = lean_apply_4(v_h__7_2353_, v_e_2377_, v_c1_2378_, v_c2_2379_, v_x_2346_);
return v___x_2380_;
}
case 7:
{
lean_object* v_e_2381_; lean_object* v_c_2382_; lean_object* v___x_2383_; 
lean_dec(v_h__10_2356_);
lean_dec(v_h__9_2355_);
lean_dec(v_h__7_2353_);
lean_dec(v_h__6_2352_);
lean_dec(v_h__5_2351_);
lean_dec(v_h__4_2350_);
lean_dec(v_h__3_2349_);
lean_dec(v_h__2_2348_);
lean_dec(v_h__1_2347_);
v_e_2381_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_e_2381_);
v_c_2382_ = lean_ctor_get(v_x_2345_, 1);
lean_inc(v_c_2382_);
lean_dec_ref(v_x_2345_);
v___x_2383_ = lean_apply_3(v_h__8_2354_, v_e_2381_, v_c_2382_, v_x_2346_);
return v___x_2383_;
}
case 8:
{
lean_object* v_e_2384_; lean_object* v___x_2385_; 
lean_dec(v_h__10_2356_);
lean_dec(v_h__8_2354_);
lean_dec(v_h__7_2353_);
lean_dec(v_h__6_2352_);
lean_dec(v_h__5_2351_);
lean_dec(v_h__4_2350_);
lean_dec(v_h__3_2349_);
lean_dec(v_h__2_2348_);
lean_dec(v_h__1_2347_);
v_e_2384_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_e_2384_);
lean_dec_ref(v_x_2345_);
v___x_2385_ = lean_apply_2(v_h__9_2355_, v_e_2384_, v_x_2346_);
return v___x_2385_;
}
default: 
{
lean_object* v_dst_2386_; lean_object* v_src_2387_; lean_object* v___x_2388_; 
lean_dec(v_h__9_2355_);
lean_dec(v_h__8_2354_);
lean_dec(v_h__7_2353_);
lean_dec(v_h__6_2352_);
lean_dec(v_h__5_2351_);
lean_dec(v_h__4_2350_);
lean_dec(v_h__3_2349_);
lean_dec(v_h__2_2348_);
lean_dec(v_h__1_2347_);
v_dst_2386_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_dst_2386_);
v_src_2387_ = lean_ctor_get(v_x_2345_, 1);
lean_inc(v_src_2387_);
lean_dec_ref(v_x_2345_);
v___x_2388_ = lean_apply_3(v_h__10_2356_, v_dst_2386_, v_src_2387_, v_x_2346_);
return v___x_2388_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__12_splitter(lean_object* v_00_u03c3_2389_, lean_object* v_motive_2390_, lean_object* v_x_2391_, lean_object* v_x_2392_, lean_object* v_h__1_2393_, lean_object* v_h__2_2394_, lean_object* v_h__3_2395_, lean_object* v_h__4_2396_, lean_object* v_h__5_2397_, lean_object* v_h__6_2398_, lean_object* v_h__7_2399_, lean_object* v_h__8_2400_, lean_object* v_h__9_2401_, lean_object* v_h__10_2402_){
_start:
{
switch(lean_obj_tag(v_x_2391_))
{
case 0:
{
lean_object* v___x_2403_; 
lean_dec(v_h__10_2402_);
lean_dec(v_h__9_2401_);
lean_dec(v_h__8_2400_);
lean_dec(v_h__7_2399_);
lean_dec(v_h__6_2398_);
lean_dec(v_h__5_2397_);
lean_dec(v_h__4_2396_);
lean_dec(v_h__3_2395_);
lean_dec(v_h__2_2394_);
v___x_2403_ = lean_apply_1(v_h__1_2393_, v_x_2392_);
return v___x_2403_;
}
case 1:
{
lean_object* v_v_2404_; lean_object* v_e_2405_; lean_object* v_cont_2406_; lean_object* v___x_2407_; 
lean_dec(v_h__10_2402_);
lean_dec(v_h__9_2401_);
lean_dec(v_h__8_2400_);
lean_dec(v_h__7_2399_);
lean_dec(v_h__6_2398_);
lean_dec(v_h__5_2397_);
lean_dec(v_h__4_2396_);
lean_dec(v_h__3_2395_);
lean_dec(v_h__1_2393_);
v_v_2404_ = lean_ctor_get(v_x_2391_, 0);
lean_inc_ref(v_v_2404_);
v_e_2405_ = lean_ctor_get(v_x_2391_, 1);
lean_inc(v_e_2405_);
v_cont_2406_ = lean_ctor_get(v_x_2391_, 2);
lean_inc(v_cont_2406_);
lean_dec_ref(v_x_2391_);
v___x_2407_ = lean_apply_4(v_h__2_2394_, v_v_2404_, v_e_2405_, v_cont_2406_, v_x_2392_);
return v___x_2407_;
}
case 2:
{
lean_object* v_v_2408_; lean_object* v_e_2409_; lean_object* v___x_2410_; 
lean_dec(v_h__10_2402_);
lean_dec(v_h__9_2401_);
lean_dec(v_h__8_2400_);
lean_dec(v_h__7_2399_);
lean_dec(v_h__6_2398_);
lean_dec(v_h__5_2397_);
lean_dec(v_h__4_2396_);
lean_dec(v_h__2_2394_);
lean_dec(v_h__1_2393_);
v_v_2408_ = lean_ctor_get(v_x_2391_, 0);
lean_inc_ref(v_v_2408_);
v_e_2409_ = lean_ctor_get(v_x_2391_, 1);
lean_inc(v_e_2409_);
lean_dec_ref(v_x_2391_);
v___x_2410_ = lean_apply_3(v_h__3_2395_, v_v_2408_, v_e_2409_, v_x_2392_);
return v___x_2410_;
}
case 3:
{
lean_object* v_dst_2411_; lean_object* v_src_2412_; lean_object* v___x_2413_; 
lean_dec(v_h__10_2402_);
lean_dec(v_h__9_2401_);
lean_dec(v_h__8_2400_);
lean_dec(v_h__7_2399_);
lean_dec(v_h__6_2398_);
lean_dec(v_h__5_2397_);
lean_dec(v_h__3_2395_);
lean_dec(v_h__2_2394_);
lean_dec(v_h__1_2393_);
v_dst_2411_ = lean_ctor_get(v_x_2391_, 0);
lean_inc(v_dst_2411_);
v_src_2412_ = lean_ctor_get(v_x_2391_, 1);
lean_inc(v_src_2412_);
lean_dec_ref(v_x_2391_);
v___x_2413_ = lean_apply_3(v_h__4_2396_, v_dst_2411_, v_src_2412_, v_x_2392_);
return v___x_2413_;
}
case 4:
{
lean_object* v_name_2414_; lean_object* v_confPtr_2415_; lean_object* v_confLen_2416_; lean_object* v_arrPtr_2417_; lean_object* v_arrLen_2418_; lean_object* v___x_2419_; 
lean_dec(v_h__10_2402_);
lean_dec(v_h__9_2401_);
lean_dec(v_h__8_2400_);
lean_dec(v_h__7_2399_);
lean_dec(v_h__6_2398_);
lean_dec(v_h__4_2396_);
lean_dec(v_h__3_2395_);
lean_dec(v_h__2_2394_);
lean_dec(v_h__1_2393_);
v_name_2414_ = lean_ctor_get(v_x_2391_, 0);
lean_inc_ref(v_name_2414_);
v_confPtr_2415_ = lean_ctor_get(v_x_2391_, 1);
lean_inc(v_confPtr_2415_);
v_confLen_2416_ = lean_ctor_get(v_x_2391_, 2);
lean_inc(v_confLen_2416_);
v_arrPtr_2417_ = lean_ctor_get(v_x_2391_, 3);
lean_inc(v_arrPtr_2417_);
v_arrLen_2418_ = lean_ctor_get(v_x_2391_, 4);
lean_inc(v_arrLen_2418_);
lean_dec_ref(v_x_2391_);
v___x_2419_ = lean_apply_6(v_h__5_2397_, v_name_2414_, v_confPtr_2415_, v_confLen_2416_, v_arrPtr_2417_, v_arrLen_2418_, v_x_2392_);
return v___x_2419_;
}
case 5:
{
lean_object* v_c1_2420_; lean_object* v_c2_2421_; lean_object* v___x_2422_; 
lean_dec(v_h__10_2402_);
lean_dec(v_h__9_2401_);
lean_dec(v_h__8_2400_);
lean_dec(v_h__7_2399_);
lean_dec(v_h__5_2397_);
lean_dec(v_h__4_2396_);
lean_dec(v_h__3_2395_);
lean_dec(v_h__2_2394_);
lean_dec(v_h__1_2393_);
v_c1_2420_ = lean_ctor_get(v_x_2391_, 0);
lean_inc(v_c1_2420_);
v_c2_2421_ = lean_ctor_get(v_x_2391_, 1);
lean_inc(v_c2_2421_);
lean_dec_ref(v_x_2391_);
v___x_2422_ = lean_apply_3(v_h__6_2398_, v_c1_2420_, v_c2_2421_, v_x_2392_);
return v___x_2422_;
}
case 6:
{
lean_object* v_e_2423_; lean_object* v_c1_2424_; lean_object* v_c2_2425_; lean_object* v___x_2426_; 
lean_dec(v_h__10_2402_);
lean_dec(v_h__9_2401_);
lean_dec(v_h__8_2400_);
lean_dec(v_h__6_2398_);
lean_dec(v_h__5_2397_);
lean_dec(v_h__4_2396_);
lean_dec(v_h__3_2395_);
lean_dec(v_h__2_2394_);
lean_dec(v_h__1_2393_);
v_e_2423_ = lean_ctor_get(v_x_2391_, 0);
lean_inc(v_e_2423_);
v_c1_2424_ = lean_ctor_get(v_x_2391_, 1);
lean_inc(v_c1_2424_);
v_c2_2425_ = lean_ctor_get(v_x_2391_, 2);
lean_inc(v_c2_2425_);
lean_dec_ref(v_x_2391_);
v___x_2426_ = lean_apply_4(v_h__7_2399_, v_e_2423_, v_c1_2424_, v_c2_2425_, v_x_2392_);
return v___x_2426_;
}
case 7:
{
lean_object* v_e_2427_; lean_object* v_c_2428_; lean_object* v___x_2429_; 
lean_dec(v_h__10_2402_);
lean_dec(v_h__9_2401_);
lean_dec(v_h__7_2399_);
lean_dec(v_h__6_2398_);
lean_dec(v_h__5_2397_);
lean_dec(v_h__4_2396_);
lean_dec(v_h__3_2395_);
lean_dec(v_h__2_2394_);
lean_dec(v_h__1_2393_);
v_e_2427_ = lean_ctor_get(v_x_2391_, 0);
lean_inc(v_e_2427_);
v_c_2428_ = lean_ctor_get(v_x_2391_, 1);
lean_inc(v_c_2428_);
lean_dec_ref(v_x_2391_);
v___x_2429_ = lean_apply_3(v_h__8_2400_, v_e_2427_, v_c_2428_, v_x_2392_);
return v___x_2429_;
}
case 8:
{
lean_object* v_e_2430_; lean_object* v___x_2431_; 
lean_dec(v_h__10_2402_);
lean_dec(v_h__8_2400_);
lean_dec(v_h__7_2399_);
lean_dec(v_h__6_2398_);
lean_dec(v_h__5_2397_);
lean_dec(v_h__4_2396_);
lean_dec(v_h__3_2395_);
lean_dec(v_h__2_2394_);
lean_dec(v_h__1_2393_);
v_e_2430_ = lean_ctor_get(v_x_2391_, 0);
lean_inc(v_e_2430_);
lean_dec_ref(v_x_2391_);
v___x_2431_ = lean_apply_2(v_h__9_2401_, v_e_2430_, v_x_2392_);
return v___x_2431_;
}
default: 
{
lean_object* v_dst_2432_; lean_object* v_src_2433_; lean_object* v___x_2434_; 
lean_dec(v_h__9_2401_);
lean_dec(v_h__8_2400_);
lean_dec(v_h__7_2399_);
lean_dec(v_h__6_2398_);
lean_dec(v_h__5_2397_);
lean_dec(v_h__4_2396_);
lean_dec(v_h__3_2395_);
lean_dec(v_h__2_2394_);
lean_dec(v_h__1_2393_);
v_dst_2432_ = lean_ctor_get(v_x_2391_, 0);
lean_inc(v_dst_2432_);
v_src_2433_ = lean_ctor_get(v_x_2391_, 1);
lean_inc(v_src_2433_);
lean_dec_ref(v_x_2391_);
v___x_2434_ = lean_apply_3(v_h__10_2402_, v_dst_2432_, v_src_2433_, v_x_2392_);
return v___x_2434_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_writeByteArray_match__1_splitter___redArg(lean_object* v_x_2435_, lean_object* v_h__1_2436_, lean_object* v_h__2_2437_){
_start:
{
if (lean_obj_tag(v_x_2435_) == 0)
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
lean_dec(v_h__1_2436_);
v___x_2438_ = lean_box(0);
v___x_2439_ = lean_apply_1(v_h__2_2437_, v___x_2438_);
return v___x_2439_;
}
else
{
lean_object* v_val_2440_; lean_object* v___x_2441_; 
lean_dec(v_h__2_2437_);
v_val_2440_ = lean_ctor_get(v_x_2435_, 0);
lean_inc(v_val_2440_);
lean_dec_ref(v_x_2435_);
v___x_2441_ = lean_apply_1(v_h__1_2436_, v_val_2440_);
return v___x_2441_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_writeByteArray_match__1_splitter(lean_object* v_motive_2442_, lean_object* v_x_2443_, lean_object* v_h__1_2444_, lean_object* v_h__2_2445_){
_start:
{
if (lean_obj_tag(v_x_2443_) == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
lean_dec(v_h__1_2444_);
v___x_2446_ = lean_box(0);
v___x_2447_ = lean_apply_1(v_h__2_2445_, v___x_2446_);
return v___x_2447_;
}
else
{
lean_object* v_val_2448_; lean_object* v___x_2449_; 
lean_dec(v_h__2_2445_);
v_val_2448_ = lean_ctor_get(v_x_2443_, 0);
lean_inc(v_val_2448_);
lean_dec_ref(v_x_2443_);
v___x_2449_ = lean_apply_1(v_h__1_2444_, v_val_2448_);
return v___x_2449_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__5_splitter___redArg(lean_object* v_x_2450_, lean_object* v_x_2451_, lean_object* v_x_2452_, lean_object* v_x_2453_, lean_object* v_h__1_2454_, lean_object* v_h__2_2455_){
_start:
{
if (lean_obj_tag(v_x_2450_) == 1)
{
if (lean_obj_tag(v_x_2451_) == 1)
{
if (lean_obj_tag(v_x_2452_) == 1)
{
if (lean_obj_tag(v_x_2453_) == 1)
{
lean_object* v_val_2456_; lean_object* v_val_2457_; lean_object* v_val_2458_; lean_object* v_val_2459_; lean_object* v___x_2460_; 
lean_dec(v_h__2_2455_);
v_val_2456_ = lean_ctor_get(v_x_2450_, 0);
lean_inc(v_val_2456_);
lean_dec_ref(v_x_2450_);
v_val_2457_ = lean_ctor_get(v_x_2451_, 0);
lean_inc(v_val_2457_);
lean_dec_ref(v_x_2451_);
v_val_2458_ = lean_ctor_get(v_x_2452_, 0);
lean_inc(v_val_2458_);
lean_dec_ref(v_x_2452_);
v_val_2459_ = lean_ctor_get(v_x_2453_, 0);
lean_inc(v_val_2459_);
lean_dec_ref(v_x_2453_);
v___x_2460_ = lean_apply_4(v_h__1_2454_, v_val_2456_, v_val_2457_, v_val_2458_, v_val_2459_);
return v___x_2460_;
}
else
{
lean_object* v___x_2461_; 
lean_dec(v_h__1_2454_);
v___x_2461_ = lean_apply_5(v_h__2_2455_, v_x_2450_, v_x_2451_, v_x_2452_, v_x_2453_, lean_box(0));
return v___x_2461_;
}
}
else
{
lean_object* v___x_2462_; 
lean_dec(v_h__1_2454_);
v___x_2462_ = lean_apply_5(v_h__2_2455_, v_x_2450_, v_x_2451_, v_x_2452_, v_x_2453_, lean_box(0));
return v___x_2462_;
}
}
else
{
lean_object* v___x_2463_; 
lean_dec(v_h__1_2454_);
v___x_2463_ = lean_apply_5(v_h__2_2455_, v_x_2450_, v_x_2451_, v_x_2452_, v_x_2453_, lean_box(0));
return v___x_2463_;
}
}
else
{
lean_object* v___x_2464_; 
lean_dec(v_h__1_2454_);
v___x_2464_ = lean_apply_5(v_h__2_2455_, v_x_2450_, v_x_2451_, v_x_2452_, v_x_2453_, lean_box(0));
return v___x_2464_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__5_splitter(lean_object* v_motive_2465_, lean_object* v_x_2466_, lean_object* v_x_2467_, lean_object* v_x_2468_, lean_object* v_x_2469_, lean_object* v_h__1_2470_, lean_object* v_h__2_2471_){
_start:
{
if (lean_obj_tag(v_x_2466_) == 1)
{
if (lean_obj_tag(v_x_2467_) == 1)
{
if (lean_obj_tag(v_x_2468_) == 1)
{
if (lean_obj_tag(v_x_2469_) == 1)
{
lean_object* v_val_2472_; lean_object* v_val_2473_; lean_object* v_val_2474_; lean_object* v_val_2475_; lean_object* v___x_2476_; 
lean_dec(v_h__2_2471_);
v_val_2472_ = lean_ctor_get(v_x_2466_, 0);
lean_inc(v_val_2472_);
lean_dec_ref(v_x_2466_);
v_val_2473_ = lean_ctor_get(v_x_2467_, 0);
lean_inc(v_val_2473_);
lean_dec_ref(v_x_2467_);
v_val_2474_ = lean_ctor_get(v_x_2468_, 0);
lean_inc(v_val_2474_);
lean_dec_ref(v_x_2468_);
v_val_2475_ = lean_ctor_get(v_x_2469_, 0);
lean_inc(v_val_2475_);
lean_dec_ref(v_x_2469_);
v___x_2476_ = lean_apply_4(v_h__1_2470_, v_val_2472_, v_val_2473_, v_val_2474_, v_val_2475_);
return v___x_2476_;
}
else
{
lean_object* v___x_2477_; 
lean_dec(v_h__1_2470_);
v___x_2477_ = lean_apply_5(v_h__2_2471_, v_x_2466_, v_x_2467_, v_x_2468_, v_x_2469_, lean_box(0));
return v___x_2477_;
}
}
else
{
lean_object* v___x_2478_; 
lean_dec(v_h__1_2470_);
v___x_2478_ = lean_apply_5(v_h__2_2471_, v_x_2466_, v_x_2467_, v_x_2468_, v_x_2469_, lean_box(0));
return v___x_2478_;
}
}
else
{
lean_object* v___x_2479_; 
lean_dec(v_h__1_2470_);
v___x_2479_ = lean_apply_5(v_h__2_2471_, v_x_2466_, v_x_2467_, v_x_2468_, v_x_2469_, lean_box(0));
return v___x_2479_;
}
}
else
{
lean_object* v___x_2480_; 
lean_dec(v_h__1_2470_);
v___x_2480_ = lean_apply_5(v_h__2_2471_, v_x_2466_, v_x_2467_, v_x_2468_, v_x_2469_, lean_box(0));
return v___x_2480_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__3_splitter___redArg(lean_object* v_x_2481_, lean_object* v_x_2482_, lean_object* v_h__1_2483_, lean_object* v_h__2_2484_){
_start:
{
if (lean_obj_tag(v_x_2481_) == 1)
{
if (lean_obj_tag(v_x_2482_) == 1)
{
lean_object* v_val_2485_; lean_object* v_val_2486_; lean_object* v___x_2487_; 
lean_dec(v_h__2_2484_);
v_val_2485_ = lean_ctor_get(v_x_2481_, 0);
lean_inc(v_val_2485_);
lean_dec_ref(v_x_2481_);
v_val_2486_ = lean_ctor_get(v_x_2482_, 0);
lean_inc(v_val_2486_);
lean_dec_ref(v_x_2482_);
v___x_2487_ = lean_apply_2(v_h__1_2483_, v_val_2485_, v_val_2486_);
return v___x_2487_;
}
else
{
lean_object* v___x_2488_; 
lean_dec(v_h__1_2483_);
v___x_2488_ = lean_apply_3(v_h__2_2484_, v_x_2481_, v_x_2482_, lean_box(0));
return v___x_2488_;
}
}
else
{
lean_object* v___x_2489_; 
lean_dec(v_h__1_2483_);
v___x_2489_ = lean_apply_3(v_h__2_2484_, v_x_2481_, v_x_2482_, lean_box(0));
return v___x_2489_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__3_splitter(lean_object* v_motive_2490_, lean_object* v_x_2491_, lean_object* v_x_2492_, lean_object* v_h__1_2493_, lean_object* v_h__2_2494_){
_start:
{
if (lean_obj_tag(v_x_2491_) == 1)
{
if (lean_obj_tag(v_x_2492_) == 1)
{
lean_object* v_val_2495_; lean_object* v_val_2496_; lean_object* v___x_2497_; 
lean_dec(v_h__2_2494_);
v_val_2495_ = lean_ctor_get(v_x_2491_, 0);
lean_inc(v_val_2495_);
lean_dec_ref(v_x_2491_);
v_val_2496_ = lean_ctor_get(v_x_2492_, 0);
lean_inc(v_val_2496_);
lean_dec_ref(v_x_2492_);
v___x_2497_ = lean_apply_2(v_h__1_2493_, v_val_2495_, v_val_2496_);
return v___x_2497_;
}
else
{
lean_object* v___x_2498_; 
lean_dec(v_h__1_2493_);
v___x_2498_ = lean_apply_3(v_h__2_2494_, v_x_2491_, v_x_2492_, lean_box(0));
return v___x_2498_;
}
}
else
{
lean_object* v___x_2499_; 
lean_dec(v_h__1_2493_);
v___x_2499_ = lean_apply_3(v_h__2_2494_, v_x_2491_, v_x_2492_, lean_box(0));
return v___x_2499_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__1_splitter___redArg(lean_object* v_x_2500_, lean_object* v_h__1_2501_, lean_object* v_h__2_2502_){
_start:
{
if (lean_obj_tag(v_x_2500_) == 0)
{
lean_object* v_outcome_2503_; lean_object* v___x_2504_; 
lean_dec(v_h__2_2502_);
v_outcome_2503_ = lean_ctor_get(v_x_2500_, 0);
lean_inc_ref(v_outcome_2503_);
lean_dec_ref(v_x_2500_);
v___x_2504_ = lean_apply_1(v_h__1_2501_, v_outcome_2503_);
return v___x_2504_;
}
else
{
lean_object* v_newState_2505_; lean_object* v_newBytes_2506_; lean_object* v___x_2507_; 
lean_dec(v_h__1_2501_);
v_newState_2505_ = lean_ctor_get(v_x_2500_, 0);
lean_inc(v_newState_2505_);
v_newBytes_2506_ = lean_ctor_get(v_x_2500_, 1);
lean_inc(v_newBytes_2506_);
lean_dec_ref(v_x_2500_);
v___x_2507_ = lean_apply_2(v_h__2_2502_, v_newState_2505_, v_newBytes_2506_);
return v___x_2507_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__1_splitter(lean_object* v_00_u03c3_2508_, lean_object* v_motive_2509_, lean_object* v_x_2510_, lean_object* v_h__1_2511_, lean_object* v_h__2_2512_){
_start:
{
if (lean_obj_tag(v_x_2510_) == 0)
{
lean_object* v_outcome_2513_; lean_object* v___x_2514_; 
lean_dec(v_h__2_2512_);
v_outcome_2513_ = lean_ctor_get(v_x_2510_, 0);
lean_inc_ref(v_outcome_2513_);
lean_dec_ref(v_x_2510_);
v___x_2514_ = lean_apply_1(v_h__1_2511_, v_outcome_2513_);
return v___x_2514_;
}
else
{
lean_object* v_newState_2515_; lean_object* v_newBytes_2516_; lean_object* v___x_2517_; 
lean_dec(v_h__1_2511_);
v_newState_2515_ = lean_ctor_get(v_x_2510_, 0);
lean_inc(v_newState_2515_);
v_newBytes_2516_ = lean_ctor_get(v_x_2510_, 1);
lean_inc(v_newBytes_2516_);
lean_dec_ref(v_x_2510_);
v___x_2517_ = lean_apply_2(v_h__2_2512_, v_newState_2515_, v_newBytes_2516_);
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__7_splitter___redArg(lean_object* v_x_2518_, lean_object* v_h__1_2519_, lean_object* v_h__2_2520_){
_start:
{
if (lean_obj_tag(v_x_2518_) == 0)
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_dec(v_h__2_2520_);
v___x_2521_ = lean_box(0);
v___x_2522_ = lean_apply_1(v_h__1_2519_, v___x_2521_);
return v___x_2522_;
}
else
{
lean_object* v_val_2523_; lean_object* v___x_2524_; 
lean_dec(v_h__1_2519_);
v_val_2523_ = lean_ctor_get(v_x_2518_, 0);
lean_inc(v_val_2523_);
lean_dec_ref(v_x_2518_);
v___x_2524_ = lean_apply_1(v_h__2_2520_, v_val_2523_);
return v___x_2524_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__7_splitter(lean_object* v_motive_2525_, lean_object* v_x_2526_, lean_object* v_h__1_2527_, lean_object* v_h__2_2528_){
_start:
{
if (lean_obj_tag(v_x_2526_) == 0)
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_dec(v_h__2_2528_);
v___x_2529_ = lean_box(0);
v___x_2530_ = lean_apply_1(v_h__1_2527_, v___x_2529_);
return v___x_2530_;
}
else
{
lean_object* v_val_2531_; lean_object* v___x_2532_; 
lean_dec(v_h__1_2527_);
v_val_2531_ = lean_ctor_get(v_x_2526_, 0);
lean_inc(v_val_2531_);
lean_dec_ref(v_x_2526_);
v___x_2532_ = lean_apply_1(v_h__2_2528_, v_val_2531_);
return v___x_2532_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__9_splitter___redArg(lean_object* v_x_2533_, lean_object* v_h__1_2534_, lean_object* v_h__2_2535_, lean_object* v_h__3_2536_, lean_object* v_h__4_2537_){
_start:
{
if (lean_obj_tag(v_x_2533_) == 0)
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
lean_dec(v_h__4_2537_);
lean_dec(v_h__3_2536_);
lean_dec(v_h__1_2534_);
v___x_2538_ = lean_box(0);
v___x_2539_ = lean_apply_1(v_h__2_2535_, v___x_2538_);
return v___x_2539_;
}
else
{
lean_object* v_val_2540_; 
lean_dec(v_h__2_2535_);
v_val_2540_ = lean_ctor_get(v_x_2533_, 0);
lean_inc(v_val_2540_);
lean_dec_ref(v_x_2533_);
switch(lean_obj_tag(v_val_2540_))
{
case 3:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec(v_h__4_2537_);
lean_dec(v_h__3_2536_);
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_apply_1(v_h__1_2534_, v___x_2541_);
return v___x_2542_;
}
case 2:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
lean_dec(v_h__4_2537_);
lean_dec(v_h__1_2534_);
v___x_2543_ = lean_box(0);
v___x_2544_ = lean_apply_1(v_h__3_2536_, v___x_2543_);
return v___x_2544_;
}
default: 
{
lean_object* v___x_2545_; 
lean_dec(v_h__3_2536_);
lean_dec(v_h__1_2534_);
v___x_2545_ = lean_apply_3(v_h__4_2537_, v_val_2540_, lean_box(0), lean_box(0));
return v___x_2545_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_Sem_0__Pancake_PancakeSem_match__9_splitter(lean_object* v_motive_2546_, lean_object* v_x_2547_, lean_object* v_h__1_2548_, lean_object* v_h__2_2549_, lean_object* v_h__3_2550_, lean_object* v_h__4_2551_){
_start:
{
if (lean_obj_tag(v_x_2547_) == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec(v_h__4_2551_);
lean_dec(v_h__3_2550_);
lean_dec(v_h__1_2548_);
v___x_2552_ = lean_box(0);
v___x_2553_ = lean_apply_1(v_h__2_2549_, v___x_2552_);
return v___x_2553_;
}
else
{
lean_object* v_val_2554_; 
lean_dec(v_h__2_2549_);
v_val_2554_ = lean_ctor_get(v_x_2547_, 0);
lean_inc(v_val_2554_);
lean_dec_ref(v_x_2547_);
switch(lean_obj_tag(v_val_2554_))
{
case 3:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
lean_dec(v_h__4_2551_);
lean_dec(v_h__3_2550_);
v___x_2555_ = lean_box(0);
v___x_2556_ = lean_apply_1(v_h__1_2548_, v___x_2555_);
return v___x_2556_;
}
case 2:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
lean_dec(v_h__4_2551_);
lean_dec(v_h__1_2548_);
v___x_2557_ = lean_box(0);
v___x_2558_ = lean_apply_1(v_h__3_2550_, v___x_2557_);
return v___x_2558_;
}
default: 
{
lean_object* v___x_2559_; 
lean_dec(v_h__3_2550_);
lean_dec(v_h__1_2548_);
v___x_2559_ = lean_apply_3(v_h__4_2551_, v_val_2554_, lean_box(0), lean_box(0));
return v___x_2559_;
}
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_Sem(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
