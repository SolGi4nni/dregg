// Lean compiler output
// Module: Pancake.StageProg
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
lean_object* l_instDecidableEqBitVec___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_ByteArray_toList(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_BitVec_repr(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
extern lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_StageProg_str_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_str(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_str___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__2_value;
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__5_value;
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__8;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__10_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "method"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__1_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__4_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__3_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__6_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__7;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "target"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__9_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__10_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__11;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__12;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__13_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__10_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__14_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_StageProg_instReprReq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq___closed__0_value;
static const lean_closure_object lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq_decEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instDecidableEqBitVec___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(8) << 1) | 1))} };
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq_decEq___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq_decEq___closed__0_value;
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_identity_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_identity_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_replace_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_replace_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_append_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_append_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Pancake.StageProg.BodyLoop.identity"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__3;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Pancake.StageProg.BodyLoop.replace"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__4_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__6_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Pancake.StageProg.BodyLoop.append"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__7_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__7_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__9_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_runBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_addHeader_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_addHeader_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_addHeaderF_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_addHeaderF_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_setStatus_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_setStatus_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_gate_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_gate_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_rewriteBody_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_rewriteBody_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_seq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_seq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_condR_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_condR_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_denoteStep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_StageProg_0__Pancake_StageProg_denoteStep_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_StageProg_0__Pancake_StageProg_denoteStep_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_compile(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_compile___boxed(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_xfoName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "X-Frame-Options"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_xfoName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_xfoName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_xfoName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_xfoName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_xfoName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_xfoVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "DENY"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_xfoVal___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_xfoVal___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_xfoVal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_xfoVal___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_xfoVal;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_noSniffName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "X-Content-Type-Options"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_noSniffName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_noSniffName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_noSniffName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_noSniffName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_noSniffName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nosniff"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__2;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_hstsName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Strict-Transport-Security"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_hstsName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_hstsName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_hstsName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_hstsName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_hstsName;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___lam__1___boxed(lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___closed__0_value;
static const lean_closure_object lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___closed__0_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___closed__1_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___closed__2_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___closed__2_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_mGET___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_mGET___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_mGET___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_mGET___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_mGET___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_mGET;
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageProg_isAllowed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_isAllowed___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageProg_methodFilter___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_methodFilter___lam__0___boxed(lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_StageProg_methodFilter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_StageProg_methodFilter___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_methodFilter___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_methodFilter___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_methodFilter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_methodFilter___closed__0_value),((lean_object*)(((size_t)(405) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_methodFilter___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_methodFilter___closed__1_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_methodFilter = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_methodFilter___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_locationName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Location"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_locationName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_locationName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_locationName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_locationName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_locationName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_locationVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "https://new.example/old"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_locationVal___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_locationVal___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_locationVal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_locationVal___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_locationVal;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_movedReason___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Moved"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_movedReason___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_movedReason___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_movedReason___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_movedReason___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_movedReason;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__0;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 4}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__1_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__5;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_redirect;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "hi"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__2;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_baseOk;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__0;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "max-age=31536000; includeSubDomains; preload"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__3;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_ctxGet;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__3;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_ctxPost;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_cfgA___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "max-age=100"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_cfgA___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_cfgA___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_cfgA___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_cfgA___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_cfgA;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageProg_cfgB___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "max-age=200"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageProg_cfgB___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageProg_cfgB___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_cfgB___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_cfgB___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_cfgB;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgA___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgA___closed__0;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgA;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgB___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgB___closed__0;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgB;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_StageProg_str_spec__0(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
if (lean_obj_tag(v_a_1_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = l_List_reverse___redArg(v_a_2_);
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_15_; 
v_head_4_ = lean_ctor_get(v_a_1_, 0);
v_tail_5_ = lean_ctor_get(v_a_1_, 1);
v_isSharedCheck_15_ = !lean_is_exclusive(v_a_1_);
if (v_isSharedCheck_15_ == 0)
{
v___x_7_ = v_a_1_;
v_isShared_8_ = v_isSharedCheck_15_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_head_4_);
lean_dec(v_a_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_15_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_12_; 
v___x_9_ = lean_unbox(v_head_4_);
lean_dec(v_head_4_);
v___x_10_ = lean_uint8_to_nat(v___x_9_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_a_2_);
lean_ctor_set(v___x_7_, 0, v___x_10_);
v___x_12_ = v___x_7_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v___x_10_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v_a_2_);
v___x_12_ = v_reuseFailAlloc_14_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
v_a_1_ = v_tail_5_;
v_a_2_ = v___x_12_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_str(lean_object* v_s_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_17_ = lean_string_to_utf8(v_s_16_);
v___x_18_ = l_ByteArray_toList(v___x_17_);
lean_dec_ref(v___x_17_);
v___x_19_ = lean_box(0);
v___x_20_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_StageProg_str_spec__0(v___x_18_, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_str___boxed(lean_object* v_s_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v_s_21_);
lean_dec_ref(v_s_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0_spec__0_spec__1(lean_object* v_x_23_, lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
if (lean_obj_tag(v_x_25_) == 0)
{
lean_dec(v_x_23_);
return v_x_24_;
}
else
{
lean_object* v_head_26_; lean_object* v_tail_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_38_; 
v_head_26_ = lean_ctor_get(v_x_25_, 0);
v_tail_27_ = lean_ctor_get(v_x_25_, 1);
v_isSharedCheck_38_ = !lean_is_exclusive(v_x_25_);
if (v_isSharedCheck_38_ == 0)
{
v___x_29_ = v_x_25_;
v_isShared_30_ = v_isSharedCheck_38_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_tail_27_);
lean_inc(v_head_26_);
lean_dec(v_x_25_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_38_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_31_ = lean_unsigned_to_nat(8u);
lean_inc(v_x_23_);
if (v_isShared_30_ == 0)
{
lean_ctor_set_tag(v___x_29_, 5);
lean_ctor_set(v___x_29_, 1, v_x_23_);
lean_ctor_set(v___x_29_, 0, v_x_24_);
v___x_33_ = v___x_29_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_x_24_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_x_23_);
v___x_33_ = v_reuseFailAlloc_37_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = l_BitVec_repr(v___x_31_, v_head_26_);
v___x_35_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_33_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
v_x_24_ = v___x_35_;
v_x_25_ = v_tail_27_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0_spec__0(lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
lean_object* v___x_41_; 
lean_dec(v_x_40_);
v___x_41_ = lean_box(0);
return v___x_41_;
}
else
{
lean_object* v_head_42_; lean_object* v_tail_43_; lean_object* v___x_44_; 
v_head_42_ = lean_ctor_get(v_x_39_, 0);
lean_inc(v_head_42_);
v_tail_43_ = lean_ctor_get(v_x_39_, 1);
lean_inc(v_tail_43_);
lean_dec_ref(v_x_39_);
v___x_44_ = lean_unsigned_to_nat(8u);
if (lean_obj_tag(v_tail_43_) == 0)
{
lean_object* v___x_45_; 
lean_dec(v_x_40_);
v___x_45_ = l_BitVec_repr(v___x_44_, v_head_42_);
return v___x_45_;
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = l_BitVec_repr(v___x_44_, v_head_42_);
v___x_47_ = lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0_spec__0_spec__1(v_x_40_, v___x_46_, v_tail_43_);
return v___x_47_;
}
}
}
}
static lean_object* _init_lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__2));
v___x_60_ = lean_string_length(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_obj_once(&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__7, &lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__7_once, _init_lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__7);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg(lean_object* v_a_67_){
_start:
{
if (lean_obj_tag(v_a_67_) == 0)
{
lean_object* v___x_68_; 
v___x_68_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__1));
return v___x_68_;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; lean_object* v___x_78_; 
v___x_69_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__5));
v___x_70_ = lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0_spec__0(v_a_67_, v___x_69_);
v___x_71_ = lean_obj_once(&lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__8, &lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__8_once, _init_lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__8);
v___x_72_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__9));
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_70_);
v___x_74_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__10));
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_71_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = 0;
v___x_78_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_78_, 0, v___x_76_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*1, v___x_77_);
return v___x_78_;
}
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_unsigned_to_nat(10u);
v___x_93_ = lean_nat_to_int(v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__0));
v___x_99_ = lean_string_length(v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__11, &lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__11);
v___x_101_ = lean_nat_to_int(v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg(lean_object* v_x_106_){
_start:
{
lean_object* v_method_107_; lean_object* v_target_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_140_; 
v_method_107_ = lean_ctor_get(v_x_106_, 0);
v_target_108_ = lean_ctor_get(v_x_106_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_x_106_);
if (v_isSharedCheck_140_ == 0)
{
v___x_110_ = v_x_106_;
v_isShared_111_ = v_isSharedCheck_140_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_target_108_);
lean_inc(v_method_107_);
lean_dec(v_x_106_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_140_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_112_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__5));
v___x_113_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__6));
v___x_114_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__7, &lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__7);
v___x_115_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg(v_method_107_);
if (v_isShared_111_ == 0)
{
lean_ctor_set_tag(v___x_110_, 4);
lean_ctor_set(v___x_110_, 1, v___x_115_);
lean_ctor_set(v___x_110_, 0, v___x_114_);
v___x_117_ = v___x_110_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_114_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_115_);
v___x_117_ = v_reuseFailAlloc_139_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_118_ = 0;
v___x_119_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_119_, 0, v___x_117_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*1, v___x_118_);
v___x_120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_113_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg___closed__4));
v___x_122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_120_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = lean_box(1);
v___x_124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_122_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__9));
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_112_);
v___x_128_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg(v_target_108_);
v___x_129_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_114_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set_uint8(v___x_130_, sizeof(void*)*1, v___x_118_);
v___x_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_127_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__12, &lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__12);
v___x_133_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__13));
v___x_134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_131_);
v___x_135_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg___closed__14));
v___x_136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_132_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*1, v___x_118_);
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr(lean_object* v_x_141_, lean_object* v_prec_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___redArg(v_x_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr___boxed(lean_object* v_x_144_, lean_object* v_prec_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = lp_orb_x2dcompiler_Pancake_StageProg_instReprReq_repr(v_x_144_, v_prec_145_);
lean_dec(v_prec_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0(lean_object* v_a_147_, lean_object* v_n_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg(v_a_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___boxed(lean_object* v_a_150_, lean_object* v_n_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0(v_a_150_, v_n_151_);
lean_dec(v_n_151_);
return v_res_152_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq_decEq(lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
lean_object* v_method_159_; lean_object* v_target_160_; lean_object* v_method_161_; lean_object* v_target_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_method_159_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_method_159_);
v_target_160_ = lean_ctor_get(v_x_157_, 1);
lean_inc(v_target_160_);
lean_dec_ref(v_x_157_);
v_method_161_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_method_161_);
v_target_162_ = lean_ctor_get(v_x_158_, 1);
lean_inc(v_target_162_);
lean_dec_ref(v_x_158_);
v___x_163_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq_decEq___closed__0));
v___x_164_ = l_instDecidableEqList___redArg(v___x_163_, v_method_159_, v_method_161_);
if (v___x_164_ == 0)
{
lean_dec(v_target_162_);
lean_dec(v_target_160_);
return v___x_164_;
}
else
{
uint8_t v___x_165_; 
v___x_165_ = l_instDecidableEqList___redArg(v___x_163_, v_target_160_, v_target_162_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq_decEq___boxed(lean_object* v_x_166_, lean_object* v_x_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq_decEq(v_x_166_, v_x_167_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq(lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq_decEq(v_x_170_, v_x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq___boxed(lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq(v_x_173_, v_x_174_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorIdx(lean_object* v_x_177_){
_start:
{
switch(lean_obj_tag(v_x_177_))
{
case 0:
{
lean_object* v___x_178_; 
v___x_178_ = lean_unsigned_to_nat(0u);
return v___x_178_;
}
case 1:
{
lean_object* v___x_179_; 
v___x_179_ = lean_unsigned_to_nat(1u);
return v___x_179_;
}
default: 
{
lean_object* v___x_180_; 
v___x_180_ = lean_unsigned_to_nat(2u);
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorIdx___boxed(lean_object* v_x_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorIdx(v_x_181_);
lean_dec(v_x_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorElim___redArg(lean_object* v_t_183_, lean_object* v_k_184_){
_start:
{
if (lean_obj_tag(v_t_183_) == 0)
{
return v_k_184_;
}
else
{
lean_object* v_b_185_; lean_object* v___x_186_; 
v_b_185_ = lean_ctor_get(v_t_183_, 0);
lean_inc(v_b_185_);
lean_dec(v_t_183_);
v___x_186_ = lean_apply_1(v_k_184_, v_b_185_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorElim(lean_object* v_motive_187_, lean_object* v_ctorIdx_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_k_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorElim___redArg(v_t_189_, v_k_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorElim___boxed(lean_object* v_motive_193_, lean_object* v_ctorIdx_194_, lean_object* v_t_195_, lean_object* v_h_196_, lean_object* v_k_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorElim(v_motive_193_, v_ctorIdx_194_, v_t_195_, v_h_196_, v_k_197_);
lean_dec(v_ctorIdx_194_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_identity_elim___redArg(lean_object* v_t_199_, lean_object* v_identity_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorElim___redArg(v_t_199_, v_identity_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_identity_elim(lean_object* v_motive_202_, lean_object* v_t_203_, lean_object* v_h_204_, lean_object* v_identity_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorElim___redArg(v_t_203_, v_identity_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_replace_elim___redArg(lean_object* v_t_207_, lean_object* v_replace_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorElim___redArg(v_t_207_, v_replace_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_replace_elim(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_replace_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorElim___redArg(v_t_211_, v_replace_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_append_elim___redArg(lean_object* v_t_215_, lean_object* v_append_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorElim___redArg(v_t_215_, v_append_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_append_elim(lean_object* v_motive_218_, lean_object* v_t_219_, lean_object* v_h_220_, lean_object* v_append_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lp_orb_x2dcompiler_Pancake_StageProg_BodyLoop_ctorElim___redArg(v_t_219_, v_append_221_);
return v___x_222_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__2(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_unsigned_to_nat(2u);
v___x_227_ = lean_nat_to_int(v___x_226_);
return v___x_227_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__3(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_nat_to_int(v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr(lean_object* v_x_242_, lean_object* v_prec_243_){
_start:
{
lean_object* v___y_245_; 
switch(lean_obj_tag(v_x_242_))
{
case 0:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = lean_unsigned_to_nat(1024u);
v___x_252_ = lean_nat_dec_le(v___x_251_, v_prec_243_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
v___x_253_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__2, &lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__2);
v___y_245_ = v___x_253_;
goto v___jp_244_;
}
else
{
lean_object* v___x_254_; 
v___x_254_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__3, &lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__3);
v___y_245_ = v___x_254_;
goto v___jp_244_;
}
}
case 1:
{
lean_object* v_b_255_; lean_object* v___y_257_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_b_255_ = lean_ctor_get(v_x_242_, 0);
lean_inc(v_b_255_);
lean_dec_ref(v_x_242_);
v___x_265_ = lean_unsigned_to_nat(1024u);
v___x_266_ = lean_nat_dec_le(v___x_265_, v_prec_243_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__2, &lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__2);
v___y_257_ = v___x_267_;
goto v___jp_256_;
}
else
{
lean_object* v___x_268_; 
v___x_268_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__3, &lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__3);
v___y_257_ = v___x_268_;
goto v___jp_256_;
}
v___jp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_258_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__6));
v___x_259_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg(v_b_255_);
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
lean_inc(v___y_257_);
v___x_261_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_261_, 0, v___y_257_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = 0;
v___x_263_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set_uint8(v___x_263_, sizeof(void*)*1, v___x_262_);
v___x_264_ = l_Repr_addAppParen(v___x_263_, v_prec_243_);
return v___x_264_;
}
}
default: 
{
lean_object* v_b_269_; lean_object* v___y_271_; lean_object* v___x_279_; uint8_t v___x_280_; 
v_b_269_ = lean_ctor_get(v_x_242_, 0);
lean_inc(v_b_269_);
lean_dec_ref(v_x_242_);
v___x_279_ = lean_unsigned_to_nat(1024u);
v___x_280_ = lean_nat_dec_le(v___x_279_, v_prec_243_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__2, &lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__2);
v___y_271_ = v___x_281_;
goto v___jp_270_;
}
else
{
lean_object* v___x_282_; 
v___x_282_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__3, &lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__3);
v___y_271_ = v___x_282_;
goto v___jp_270_;
}
v___jp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_272_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__9));
v___x_273_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg(v_b_269_);
v___x_274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
lean_inc(v___y_271_);
v___x_275_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_275_, 0, v___y_271_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = 0;
v___x_277_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*1, v___x_276_);
v___x_278_ = l_Repr_addAppParen(v___x_277_, v_prec_243_);
return v___x_278_;
}
}
}
v___jp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_246_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___closed__1));
lean_inc(v___y_245_);
v___x_247_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_247_, 0, v___y_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = 0;
v___x_249_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set_uint8(v___x_249_, sizeof(void*)*1, v___x_248_);
v___x_250_ = l_Repr_addAppParen(v___x_249_, v_prec_243_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr___boxed(lean_object* v_x_283_, lean_object* v_prec_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = lp_orb_x2dcompiler_Pancake_StageProg_instReprBodyLoop_repr(v_x_283_, v_prec_284_);
lean_dec(v_prec_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_runBody(lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
switch(lean_obj_tag(v_x_288_))
{
case 0:
{
return v_x_289_;
}
case 1:
{
lean_object* v_b_290_; 
lean_dec(v_x_289_);
v_b_290_ = lean_ctor_get(v_x_288_, 0);
lean_inc(v_b_290_);
lean_dec_ref(v_x_288_);
return v_b_290_;
}
default: 
{
lean_object* v_b_291_; lean_object* v___x_292_; 
v_b_291_ = lean_ctor_get(v_x_288_, 0);
lean_inc(v_b_291_);
lean_dec_ref(v_x_288_);
v___x_292_ = l_List_appendTR___redArg(v_x_289_, v_b_291_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorIdx(lean_object* v_x_293_){
_start:
{
switch(lean_obj_tag(v_x_293_))
{
case 0:
{
lean_object* v___x_294_; 
v___x_294_ = lean_unsigned_to_nat(0u);
return v___x_294_;
}
case 1:
{
lean_object* v___x_295_; 
v___x_295_ = lean_unsigned_to_nat(1u);
return v___x_295_;
}
case 2:
{
lean_object* v___x_296_; 
v___x_296_ = lean_unsigned_to_nat(2u);
return v___x_296_;
}
case 3:
{
lean_object* v___x_297_; 
v___x_297_ = lean_unsigned_to_nat(3u);
return v___x_297_;
}
case 4:
{
lean_object* v___x_298_; 
v___x_298_ = lean_unsigned_to_nat(4u);
return v___x_298_;
}
case 5:
{
lean_object* v___x_299_; 
v___x_299_ = lean_unsigned_to_nat(5u);
return v___x_299_;
}
default: 
{
lean_object* v___x_300_; 
v___x_300_ = lean_unsigned_to_nat(6u);
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorIdx___boxed(lean_object* v_x_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorIdx(v_x_301_);
lean_dec_ref(v_x_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(lean_object* v_t_303_, lean_object* v_k_304_){
_start:
{
switch(lean_obj_tag(v_t_303_))
{
case 1:
{
lean_object* v_nameF_305_; lean_object* v_valF_306_; lean_object* v___x_307_; 
v_nameF_305_ = lean_ctor_get(v_t_303_, 0);
lean_inc_ref(v_nameF_305_);
v_valF_306_ = lean_ctor_get(v_t_303_, 1);
lean_inc_ref(v_valF_306_);
lean_dec_ref(v_t_303_);
v___x_307_ = lean_apply_2(v_k_304_, v_nameF_305_, v_valF_306_);
return v___x_307_;
}
case 3:
{
lean_object* v_c_308_; lean_object* v_code_309_; lean_object* v___x_310_; 
v_c_308_ = lean_ctor_get(v_t_303_, 0);
lean_inc_ref(v_c_308_);
v_code_309_ = lean_ctor_get(v_t_303_, 1);
lean_inc(v_code_309_);
lean_dec_ref(v_t_303_);
v___x_310_ = lean_apply_2(v_k_304_, v_c_308_, v_code_309_);
return v___x_310_;
}
case 4:
{
lean_object* v_t_311_; lean_object* v___x_312_; 
v_t_311_ = lean_ctor_get(v_t_303_, 0);
lean_inc(v_t_311_);
lean_dec_ref(v_t_303_);
v___x_312_ = lean_apply_1(v_k_304_, v_t_311_);
return v___x_312_;
}
case 5:
{
lean_object* v_a_313_; lean_object* v_b_314_; lean_object* v___x_315_; 
v_a_313_ = lean_ctor_get(v_t_303_, 0);
lean_inc_ref(v_a_313_);
v_b_314_ = lean_ctor_get(v_t_303_, 1);
lean_inc_ref(v_b_314_);
lean_dec_ref(v_t_303_);
v___x_315_ = lean_apply_2(v_k_304_, v_a_313_, v_b_314_);
return v___x_315_;
}
case 6:
{
lean_object* v_c_316_; lean_object* v_a_317_; lean_object* v_b_318_; lean_object* v___x_319_; 
v_c_316_ = lean_ctor_get(v_t_303_, 0);
lean_inc_ref(v_c_316_);
v_a_317_ = lean_ctor_get(v_t_303_, 1);
lean_inc_ref(v_a_317_);
v_b_318_ = lean_ctor_get(v_t_303_, 2);
lean_inc_ref(v_b_318_);
lean_dec_ref(v_t_303_);
v___x_319_ = lean_apply_3(v_k_304_, v_c_316_, v_a_317_, v_b_318_);
return v___x_319_;
}
default: 
{
lean_object* v_name_320_; lean_object* v_val_321_; lean_object* v___x_322_; 
v_name_320_ = lean_ctor_get(v_t_303_, 0);
lean_inc(v_name_320_);
v_val_321_ = lean_ctor_get(v_t_303_, 1);
lean_inc(v_val_321_);
lean_dec_ref(v_t_303_);
v___x_322_ = lean_apply_2(v_k_304_, v_name_320_, v_val_321_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim(lean_object* v_motive_323_, lean_object* v_ctorIdx_324_, lean_object* v_t_325_, lean_object* v_h_326_, lean_object* v_k_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(v_t_325_, v_k_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___boxed(lean_object* v_motive_329_, lean_object* v_ctorIdx_330_, lean_object* v_t_331_, lean_object* v_h_332_, lean_object* v_k_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim(v_motive_329_, v_ctorIdx_330_, v_t_331_, v_h_332_, v_k_333_);
lean_dec(v_ctorIdx_330_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_addHeader_elim___redArg(lean_object* v_t_335_, lean_object* v_addHeader_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(v_t_335_, v_addHeader_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_addHeader_elim(lean_object* v_motive_338_, lean_object* v_t_339_, lean_object* v_h_340_, lean_object* v_addHeader_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(v_t_339_, v_addHeader_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_addHeaderF_elim___redArg(lean_object* v_t_343_, lean_object* v_addHeaderF_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(v_t_343_, v_addHeaderF_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_addHeaderF_elim(lean_object* v_motive_346_, lean_object* v_t_347_, lean_object* v_h_348_, lean_object* v_addHeaderF_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(v_t_347_, v_addHeaderF_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_setStatus_elim___redArg(lean_object* v_t_351_, lean_object* v_setStatus_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(v_t_351_, v_setStatus_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_setStatus_elim(lean_object* v_motive_354_, lean_object* v_t_355_, lean_object* v_h_356_, lean_object* v_setStatus_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(v_t_355_, v_setStatus_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_gate_elim___redArg(lean_object* v_t_359_, lean_object* v_gate_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(v_t_359_, v_gate_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_gate_elim(lean_object* v_motive_362_, lean_object* v_t_363_, lean_object* v_h_364_, lean_object* v_gate_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(v_t_363_, v_gate_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_rewriteBody_elim___redArg(lean_object* v_t_367_, lean_object* v_rewriteBody_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(v_t_367_, v_rewriteBody_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_rewriteBody_elim(lean_object* v_motive_370_, lean_object* v_t_371_, lean_object* v_h_372_, lean_object* v_rewriteBody_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(v_t_371_, v_rewriteBody_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_seq_elim___redArg(lean_object* v_t_375_, lean_object* v_seq_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(v_t_375_, v_seq_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_seq_elim(lean_object* v_motive_378_, lean_object* v_t_379_, lean_object* v_h_380_, lean_object* v_seq_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(v_t_379_, v_seq_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_condR_elim___redArg(lean_object* v_t_383_, lean_object* v_condR_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(v_t_383_, v_condR_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_StageProg_condR_elim(lean_object* v_motive_386_, lean_object* v_t_387_, lean_object* v_h_388_, lean_object* v_condR_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = lp_orb_x2dcompiler_Pancake_StageProg_StageProg_ctorElim___redArg(v_t_387_, v_condR_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_denoteStep(lean_object* v_ctx_391_, lean_object* v_x_392_, lean_object* v_x_393_){
_start:
{
switch(lean_obj_tag(v_x_392_))
{
case 0:
{
uint8_t v_halted_394_; 
lean_dec_ref(v_ctx_391_);
v_halted_394_ = lean_ctor_get_uint8(v_x_393_, sizeof(void*)*1);
if (v_halted_394_ == 0)
{
lean_object* v_resp_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_425_; 
v_resp_395_ = lean_ctor_get(v_x_393_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v_x_393_);
if (v_isSharedCheck_425_ == 0)
{
v___x_397_ = v_x_393_;
v_isShared_398_ = v_isSharedCheck_425_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_resp_395_);
lean_dec(v_x_393_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_425_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v_name_399_; lean_object* v_val_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_424_; 
v_name_399_ = lean_ctor_get(v_x_392_, 0);
v_val_400_ = lean_ctor_get(v_x_392_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v_x_392_);
if (v_isSharedCheck_424_ == 0)
{
v___x_402_ = v_x_392_;
v_isShared_403_ = v_isSharedCheck_424_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_val_400_);
lean_inc(v_name_399_);
lean_dec(v_x_392_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_424_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v_status_404_; lean_object* v_reason_405_; lean_object* v_headers_406_; lean_object* v_body_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_423_; 
v_status_404_ = lean_ctor_get(v_resp_395_, 0);
v_reason_405_ = lean_ctor_get(v_resp_395_, 1);
v_headers_406_ = lean_ctor_get(v_resp_395_, 2);
v_body_407_ = lean_ctor_get(v_resp_395_, 3);
v_isSharedCheck_423_ = !lean_is_exclusive(v_resp_395_);
if (v_isSharedCheck_423_ == 0)
{
v___x_409_ = v_resp_395_;
v_isShared_410_ = v_isSharedCheck_423_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_body_407_);
lean_inc(v_headers_406_);
lean_inc(v_reason_405_);
lean_inc(v_status_404_);
lean_dec(v_resp_395_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_423_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_403_ == 0)
{
v___x_412_ = v___x_402_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_name_399_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_val_400_);
v___x_412_ = v_reuseFailAlloc_422_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_413_ = lean_box(0);
v___x_414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_412_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = l_List_appendTR___redArg(v_headers_406_, v___x_414_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 2, v___x_415_);
v___x_417_ = v___x_409_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_status_404_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_reason_405_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_421_, 3, v_body_407_);
v___x_417_ = v_reuseFailAlloc_421_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_419_; 
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_417_);
v___x_419_ = v___x_397_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_420_, sizeof(void*)*1, v_halted_394_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_x_392_);
return v_x_393_;
}
}
case 1:
{
uint8_t v_halted_426_; 
v_halted_426_ = lean_ctor_get_uint8(v_x_393_, sizeof(void*)*1);
if (v_halted_426_ == 0)
{
lean_object* v_resp_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_459_; 
v_resp_427_ = lean_ctor_get(v_x_393_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v_x_393_);
if (v_isSharedCheck_459_ == 0)
{
v___x_429_ = v_x_393_;
v_isShared_430_ = v_isSharedCheck_459_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_resp_427_);
lean_dec(v_x_393_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_459_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_nameF_431_; lean_object* v_valF_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_458_; 
v_nameF_431_ = lean_ctor_get(v_x_392_, 0);
v_valF_432_ = lean_ctor_get(v_x_392_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_392_);
if (v_isSharedCheck_458_ == 0)
{
v___x_434_ = v_x_392_;
v_isShared_435_ = v_isSharedCheck_458_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_valF_432_);
lean_inc(v_nameF_431_);
lean_dec(v_x_392_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_458_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_status_436_; lean_object* v_reason_437_; lean_object* v_headers_438_; lean_object* v_body_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_457_; 
v_status_436_ = lean_ctor_get(v_resp_427_, 0);
v_reason_437_ = lean_ctor_get(v_resp_427_, 1);
v_headers_438_ = lean_ctor_get(v_resp_427_, 2);
v_body_439_ = lean_ctor_get(v_resp_427_, 3);
v_isSharedCheck_457_ = !lean_is_exclusive(v_resp_427_);
if (v_isSharedCheck_457_ == 0)
{
v___x_441_ = v_resp_427_;
v_isShared_442_ = v_isSharedCheck_457_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_body_439_);
lean_inc(v_headers_438_);
lean_inc(v_reason_437_);
lean_inc(v_status_436_);
lean_dec(v_resp_427_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_457_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
lean_inc_ref(v_ctx_391_);
v___x_443_ = lean_apply_1(v_nameF_431_, v_ctx_391_);
v___x_444_ = lean_apply_1(v_valF_432_, v_ctx_391_);
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 0);
lean_ctor_set(v___x_434_, 1, v___x_444_);
lean_ctor_set(v___x_434_, 0, v___x_443_);
v___x_446_ = v___x_434_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_444_);
v___x_446_ = v_reuseFailAlloc_456_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_447_ = lean_box(0);
v___x_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = l_List_appendTR___redArg(v_headers_438_, v___x_448_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 2, v___x_449_);
v___x_451_ = v___x_441_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_status_436_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_reason_437_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_body_439_);
v___x_451_ = v_reuseFailAlloc_455_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_453_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_451_);
v___x_453_ = v___x_429_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
lean_ctor_set_uint8(v_reuseFailAlloc_454_, sizeof(void*)*1, v_halted_426_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_x_392_);
lean_dec_ref(v_ctx_391_);
return v_x_393_;
}
}
case 2:
{
uint8_t v_halted_460_; 
lean_dec_ref(v_ctx_391_);
v_halted_460_ = lean_ctor_get_uint8(v_x_393_, sizeof(void*)*1);
if (v_halted_460_ == 0)
{
lean_object* v_resp_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_481_; 
v_resp_461_ = lean_ctor_get(v_x_393_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v_x_393_);
if (v_isSharedCheck_481_ == 0)
{
v___x_463_ = v_x_393_;
v_isShared_464_ = v_isSharedCheck_481_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_resp_461_);
lean_dec(v_x_393_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_481_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v_code_465_; lean_object* v_reason_466_; lean_object* v_headers_467_; lean_object* v_body_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_478_; 
v_code_465_ = lean_ctor_get(v_x_392_, 0);
lean_inc(v_code_465_);
v_reason_466_ = lean_ctor_get(v_x_392_, 1);
lean_inc(v_reason_466_);
lean_dec_ref(v_x_392_);
v_headers_467_ = lean_ctor_get(v_resp_461_, 2);
v_body_468_ = lean_ctor_get(v_resp_461_, 3);
v_isSharedCheck_478_ = !lean_is_exclusive(v_resp_461_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; lean_object* v_unused_480_; 
v_unused_479_ = lean_ctor_get(v_resp_461_, 1);
lean_dec(v_unused_479_);
v_unused_480_ = lean_ctor_get(v_resp_461_, 0);
lean_dec(v_unused_480_);
v___x_470_ = v_resp_461_;
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_body_468_);
lean_inc(v_headers_467_);
lean_dec(v_resp_461_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v_reason_466_);
lean_ctor_set(v___x_470_, 0, v_code_465_);
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_code_465_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_reason_466_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_headers_467_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v_body_468_);
v___x_473_ = v_reuseFailAlloc_477_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_475_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_473_);
v___x_475_ = v___x_463_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_476_, sizeof(void*)*1, v_halted_460_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_392_);
return v_x_393_;
}
}
case 3:
{
uint8_t v_halted_482_; 
v_halted_482_ = lean_ctor_get_uint8(v_x_393_, sizeof(void*)*1);
if (v_halted_482_ == 0)
{
lean_object* v_c_483_; lean_object* v_code_484_; lean_object* v_resp_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_c_483_ = lean_ctor_get(v_x_392_, 0);
lean_inc_ref(v_c_483_);
v_code_484_ = lean_ctor_get(v_x_392_, 1);
lean_inc(v_code_484_);
lean_dec_ref(v_x_392_);
v_resp_485_ = lean_ctor_get(v_x_393_, 0);
lean_inc_ref(v_resp_485_);
v___x_486_ = lean_apply_1(v_c_483_, v_ctx_391_);
v___x_487_ = lean_unbox(v___x_486_);
if (v___x_487_ == 0)
{
lean_dec_ref(v_resp_485_);
lean_dec(v_code_484_);
return v_x_393_;
}
else
{
lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_506_; 
v_isSharedCheck_506_ = !lean_is_exclusive(v_x_393_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v_x_393_, 0);
lean_dec(v_unused_507_);
v___x_489_ = v_x_393_;
v_isShared_490_ = v_isSharedCheck_506_;
goto v_resetjp_488_;
}
else
{
lean_dec(v_x_393_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_506_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v_reason_491_; lean_object* v_headers_492_; lean_object* v_body_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_504_; 
v_reason_491_ = lean_ctor_get(v_resp_485_, 1);
v_headers_492_ = lean_ctor_get(v_resp_485_, 2);
v_body_493_ = lean_ctor_get(v_resp_485_, 3);
v_isSharedCheck_504_ = !lean_is_exclusive(v_resp_485_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; 
v_unused_505_ = lean_ctor_get(v_resp_485_, 0);
lean_dec(v_unused_505_);
v___x_495_ = v_resp_485_;
v_isShared_496_ = v_isSharedCheck_504_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_body_493_);
lean_inc(v_headers_492_);
lean_inc(v_reason_491_);
lean_dec(v_resp_485_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_504_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v_code_484_);
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_code_484_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_reason_491_);
lean_ctor_set(v_reuseFailAlloc_503_, 2, v_headers_492_);
lean_ctor_set(v_reuseFailAlloc_503_, 3, v_body_493_);
v___x_498_ = v_reuseFailAlloc_503_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_500_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_498_);
v___x_500_ = v___x_489_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_502_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
uint8_t v___x_501_; 
v___x_501_ = lean_unbox(v___x_486_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*1, v___x_501_);
return v___x_500_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_x_392_);
lean_dec_ref(v_ctx_391_);
return v_x_393_;
}
}
case 4:
{
uint8_t v_halted_508_; 
lean_dec_ref(v_ctx_391_);
v_halted_508_ = lean_ctor_get_uint8(v_x_393_, sizeof(void*)*1);
if (v_halted_508_ == 0)
{
lean_object* v_resp_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_529_; 
v_resp_509_ = lean_ctor_get(v_x_393_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v_x_393_);
if (v_isSharedCheck_529_ == 0)
{
v___x_511_ = v_x_393_;
v_isShared_512_ = v_isSharedCheck_529_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_resp_509_);
lean_dec(v_x_393_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_529_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_t_513_; lean_object* v_status_514_; lean_object* v_reason_515_; lean_object* v_headers_516_; lean_object* v_body_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_528_; 
v_t_513_ = lean_ctor_get(v_x_392_, 0);
lean_inc(v_t_513_);
lean_dec_ref(v_x_392_);
v_status_514_ = lean_ctor_get(v_resp_509_, 0);
v_reason_515_ = lean_ctor_get(v_resp_509_, 1);
v_headers_516_ = lean_ctor_get(v_resp_509_, 2);
v_body_517_ = lean_ctor_get(v_resp_509_, 3);
v_isSharedCheck_528_ = !lean_is_exclusive(v_resp_509_);
if (v_isSharedCheck_528_ == 0)
{
v___x_519_ = v_resp_509_;
v_isShared_520_ = v_isSharedCheck_528_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_body_517_);
lean_inc(v_headers_516_);
lean_inc(v_reason_515_);
lean_inc(v_status_514_);
lean_dec(v_resp_509_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_528_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_521_ = lp_orb_x2dcompiler_Pancake_StageProg_runBody(v_t_513_, v_body_517_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 3, v___x_521_);
v___x_523_ = v___x_519_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_status_514_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_reason_515_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_headers_516_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v___x_521_);
v___x_523_ = v_reuseFailAlloc_527_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_525_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_523_);
v___x_525_ = v___x_511_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
lean_ctor_set_uint8(v_reuseFailAlloc_526_, sizeof(void*)*1, v_halted_508_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_392_);
return v_x_393_;
}
}
case 5:
{
lean_object* v_a_530_; lean_object* v_b_531_; lean_object* v___x_532_; 
v_a_530_ = lean_ctor_get(v_x_392_, 0);
lean_inc_ref(v_a_530_);
v_b_531_ = lean_ctor_get(v_x_392_, 1);
lean_inc_ref(v_b_531_);
lean_dec_ref(v_x_392_);
lean_inc_ref(v_ctx_391_);
v___x_532_ = lp_orb_x2dcompiler_Pancake_StageProg_denoteStep(v_ctx_391_, v_a_530_, v_x_393_);
v_x_392_ = v_b_531_;
v_x_393_ = v___x_532_;
goto _start;
}
default: 
{
lean_object* v_c_534_; lean_object* v_a_535_; lean_object* v_b_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_c_534_ = lean_ctor_get(v_x_392_, 0);
lean_inc_ref(v_c_534_);
v_a_535_ = lean_ctor_get(v_x_392_, 1);
lean_inc_ref(v_a_535_);
v_b_536_ = lean_ctor_get(v_x_392_, 2);
lean_inc_ref(v_b_536_);
lean_dec_ref(v_x_392_);
lean_inc_ref(v_ctx_391_);
v___x_537_ = lean_apply_1(v_c_534_, v_ctx_391_);
v___x_538_ = lean_unbox(v___x_537_);
if (v___x_538_ == 0)
{
lean_dec_ref(v_a_535_);
v_x_392_ = v_b_536_;
goto _start;
}
else
{
lean_dec_ref(v_b_536_);
v_x_392_ = v_a_535_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_denote(lean_object* v_p_541_, lean_object* v_ctx_542_){
_start:
{
lean_object* v_base_543_; uint8_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_resp_547_; 
v_base_543_ = lean_ctor_get(v_ctx_542_, 1);
v___x_544_ = 0;
lean_inc_ref(v_base_543_);
v___x_545_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_545_, 0, v_base_543_);
lean_ctor_set_uint8(v___x_545_, sizeof(void*)*1, v___x_544_);
v___x_546_ = lp_orb_x2dcompiler_Pancake_StageProg_denoteStep(v_ctx_542_, v_p_541_, v___x_545_);
v_resp_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc_ref(v_resp_547_);
lean_dec_ref(v___x_546_);
return v_resp_547_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_StageProg_0__Pancake_StageProg_denoteStep_match__1_splitter___redArg(lean_object* v_x_548_, lean_object* v_x_549_, lean_object* v_h__1_550_, lean_object* v_h__2_551_, lean_object* v_h__3_552_, lean_object* v_h__4_553_, lean_object* v_h__5_554_, lean_object* v_h__6_555_, lean_object* v_h__7_556_){
_start:
{
switch(lean_obj_tag(v_x_548_))
{
case 0:
{
lean_object* v_name_557_; lean_object* v_val_558_; lean_object* v___x_559_; 
lean_dec(v_h__7_556_);
lean_dec(v_h__6_555_);
lean_dec(v_h__5_554_);
lean_dec(v_h__4_553_);
lean_dec(v_h__3_552_);
lean_dec(v_h__2_551_);
v_name_557_ = lean_ctor_get(v_x_548_, 0);
lean_inc(v_name_557_);
v_val_558_ = lean_ctor_get(v_x_548_, 1);
lean_inc(v_val_558_);
lean_dec_ref(v_x_548_);
v___x_559_ = lean_apply_3(v_h__1_550_, v_name_557_, v_val_558_, v_x_549_);
return v___x_559_;
}
case 1:
{
lean_object* v_nameF_560_; lean_object* v_valF_561_; lean_object* v___x_562_; 
lean_dec(v_h__7_556_);
lean_dec(v_h__6_555_);
lean_dec(v_h__5_554_);
lean_dec(v_h__4_553_);
lean_dec(v_h__3_552_);
lean_dec(v_h__1_550_);
v_nameF_560_ = lean_ctor_get(v_x_548_, 0);
lean_inc_ref(v_nameF_560_);
v_valF_561_ = lean_ctor_get(v_x_548_, 1);
lean_inc_ref(v_valF_561_);
lean_dec_ref(v_x_548_);
v___x_562_ = lean_apply_3(v_h__2_551_, v_nameF_560_, v_valF_561_, v_x_549_);
return v___x_562_;
}
case 2:
{
lean_object* v_code_563_; lean_object* v_reason_564_; lean_object* v___x_565_; 
lean_dec(v_h__7_556_);
lean_dec(v_h__6_555_);
lean_dec(v_h__5_554_);
lean_dec(v_h__4_553_);
lean_dec(v_h__2_551_);
lean_dec(v_h__1_550_);
v_code_563_ = lean_ctor_get(v_x_548_, 0);
lean_inc(v_code_563_);
v_reason_564_ = lean_ctor_get(v_x_548_, 1);
lean_inc(v_reason_564_);
lean_dec_ref(v_x_548_);
v___x_565_ = lean_apply_3(v_h__3_552_, v_code_563_, v_reason_564_, v_x_549_);
return v___x_565_;
}
case 3:
{
lean_object* v_c_566_; lean_object* v_code_567_; lean_object* v___x_568_; 
lean_dec(v_h__7_556_);
lean_dec(v_h__6_555_);
lean_dec(v_h__5_554_);
lean_dec(v_h__3_552_);
lean_dec(v_h__2_551_);
lean_dec(v_h__1_550_);
v_c_566_ = lean_ctor_get(v_x_548_, 0);
lean_inc_ref(v_c_566_);
v_code_567_ = lean_ctor_get(v_x_548_, 1);
lean_inc(v_code_567_);
lean_dec_ref(v_x_548_);
v___x_568_ = lean_apply_3(v_h__4_553_, v_c_566_, v_code_567_, v_x_549_);
return v___x_568_;
}
case 4:
{
lean_object* v_t_569_; lean_object* v___x_570_; 
lean_dec(v_h__7_556_);
lean_dec(v_h__6_555_);
lean_dec(v_h__4_553_);
lean_dec(v_h__3_552_);
lean_dec(v_h__2_551_);
lean_dec(v_h__1_550_);
v_t_569_ = lean_ctor_get(v_x_548_, 0);
lean_inc(v_t_569_);
lean_dec_ref(v_x_548_);
v___x_570_ = lean_apply_2(v_h__5_554_, v_t_569_, v_x_549_);
return v___x_570_;
}
case 5:
{
lean_object* v_a_571_; lean_object* v_b_572_; lean_object* v___x_573_; 
lean_dec(v_h__7_556_);
lean_dec(v_h__5_554_);
lean_dec(v_h__4_553_);
lean_dec(v_h__3_552_);
lean_dec(v_h__2_551_);
lean_dec(v_h__1_550_);
v_a_571_ = lean_ctor_get(v_x_548_, 0);
lean_inc_ref(v_a_571_);
v_b_572_ = lean_ctor_get(v_x_548_, 1);
lean_inc_ref(v_b_572_);
lean_dec_ref(v_x_548_);
v___x_573_ = lean_apply_3(v_h__6_555_, v_a_571_, v_b_572_, v_x_549_);
return v___x_573_;
}
default: 
{
lean_object* v_c_574_; lean_object* v_a_575_; lean_object* v_b_576_; lean_object* v___x_577_; 
lean_dec(v_h__6_555_);
lean_dec(v_h__5_554_);
lean_dec(v_h__4_553_);
lean_dec(v_h__3_552_);
lean_dec(v_h__2_551_);
lean_dec(v_h__1_550_);
v_c_574_ = lean_ctor_get(v_x_548_, 0);
lean_inc_ref(v_c_574_);
v_a_575_ = lean_ctor_get(v_x_548_, 1);
lean_inc_ref(v_a_575_);
v_b_576_ = lean_ctor_get(v_x_548_, 2);
lean_inc_ref(v_b_576_);
lean_dec_ref(v_x_548_);
v___x_577_ = lean_apply_4(v_h__7_556_, v_c_574_, v_a_575_, v_b_576_, v_x_549_);
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_StageProg_0__Pancake_StageProg_denoteStep_match__1_splitter(lean_object* v_motive_578_, lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v_h__1_581_, lean_object* v_h__2_582_, lean_object* v_h__3_583_, lean_object* v_h__4_584_, lean_object* v_h__5_585_, lean_object* v_h__6_586_, lean_object* v_h__7_587_){
_start:
{
switch(lean_obj_tag(v_x_579_))
{
case 0:
{
lean_object* v_name_588_; lean_object* v_val_589_; lean_object* v___x_590_; 
lean_dec(v_h__7_587_);
lean_dec(v_h__6_586_);
lean_dec(v_h__5_585_);
lean_dec(v_h__4_584_);
lean_dec(v_h__3_583_);
lean_dec(v_h__2_582_);
v_name_588_ = lean_ctor_get(v_x_579_, 0);
lean_inc(v_name_588_);
v_val_589_ = lean_ctor_get(v_x_579_, 1);
lean_inc(v_val_589_);
lean_dec_ref(v_x_579_);
v___x_590_ = lean_apply_3(v_h__1_581_, v_name_588_, v_val_589_, v_x_580_);
return v___x_590_;
}
case 1:
{
lean_object* v_nameF_591_; lean_object* v_valF_592_; lean_object* v___x_593_; 
lean_dec(v_h__7_587_);
lean_dec(v_h__6_586_);
lean_dec(v_h__5_585_);
lean_dec(v_h__4_584_);
lean_dec(v_h__3_583_);
lean_dec(v_h__1_581_);
v_nameF_591_ = lean_ctor_get(v_x_579_, 0);
lean_inc_ref(v_nameF_591_);
v_valF_592_ = lean_ctor_get(v_x_579_, 1);
lean_inc_ref(v_valF_592_);
lean_dec_ref(v_x_579_);
v___x_593_ = lean_apply_3(v_h__2_582_, v_nameF_591_, v_valF_592_, v_x_580_);
return v___x_593_;
}
case 2:
{
lean_object* v_code_594_; lean_object* v_reason_595_; lean_object* v___x_596_; 
lean_dec(v_h__7_587_);
lean_dec(v_h__6_586_);
lean_dec(v_h__5_585_);
lean_dec(v_h__4_584_);
lean_dec(v_h__2_582_);
lean_dec(v_h__1_581_);
v_code_594_ = lean_ctor_get(v_x_579_, 0);
lean_inc(v_code_594_);
v_reason_595_ = lean_ctor_get(v_x_579_, 1);
lean_inc(v_reason_595_);
lean_dec_ref(v_x_579_);
v___x_596_ = lean_apply_3(v_h__3_583_, v_code_594_, v_reason_595_, v_x_580_);
return v___x_596_;
}
case 3:
{
lean_object* v_c_597_; lean_object* v_code_598_; lean_object* v___x_599_; 
lean_dec(v_h__7_587_);
lean_dec(v_h__6_586_);
lean_dec(v_h__5_585_);
lean_dec(v_h__3_583_);
lean_dec(v_h__2_582_);
lean_dec(v_h__1_581_);
v_c_597_ = lean_ctor_get(v_x_579_, 0);
lean_inc_ref(v_c_597_);
v_code_598_ = lean_ctor_get(v_x_579_, 1);
lean_inc(v_code_598_);
lean_dec_ref(v_x_579_);
v___x_599_ = lean_apply_3(v_h__4_584_, v_c_597_, v_code_598_, v_x_580_);
return v___x_599_;
}
case 4:
{
lean_object* v_t_600_; lean_object* v___x_601_; 
lean_dec(v_h__7_587_);
lean_dec(v_h__6_586_);
lean_dec(v_h__4_584_);
lean_dec(v_h__3_583_);
lean_dec(v_h__2_582_);
lean_dec(v_h__1_581_);
v_t_600_ = lean_ctor_get(v_x_579_, 0);
lean_inc(v_t_600_);
lean_dec_ref(v_x_579_);
v___x_601_ = lean_apply_2(v_h__5_585_, v_t_600_, v_x_580_);
return v___x_601_;
}
case 5:
{
lean_object* v_a_602_; lean_object* v_b_603_; lean_object* v___x_604_; 
lean_dec(v_h__7_587_);
lean_dec(v_h__5_585_);
lean_dec(v_h__4_584_);
lean_dec(v_h__3_583_);
lean_dec(v_h__2_582_);
lean_dec(v_h__1_581_);
v_a_602_ = lean_ctor_get(v_x_579_, 0);
lean_inc_ref(v_a_602_);
v_b_603_ = lean_ctor_get(v_x_579_, 1);
lean_inc_ref(v_b_603_);
lean_dec_ref(v_x_579_);
v___x_604_ = lean_apply_3(v_h__6_586_, v_a_602_, v_b_603_, v_x_580_);
return v___x_604_;
}
default: 
{
lean_object* v_c_605_; lean_object* v_a_606_; lean_object* v_b_607_; lean_object* v___x_608_; 
lean_dec(v_h__6_586_);
lean_dec(v_h__5_585_);
lean_dec(v_h__4_584_);
lean_dec(v_h__3_583_);
lean_dec(v_h__2_582_);
lean_dec(v_h__1_581_);
v_c_605_ = lean_ctor_get(v_x_579_, 0);
lean_inc_ref(v_c_605_);
v_a_606_ = lean_ctor_get(v_x_579_, 1);
lean_inc_ref(v_a_606_);
v_b_607_ = lean_ctor_get(v_x_579_, 2);
lean_inc_ref(v_b_607_);
lean_dec_ref(v_x_579_);
v___x_608_ = lean_apply_4(v_h__7_587_, v_c_605_, v_a_606_, v_b_607_, v_x_580_);
return v___x_608_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_compile(lean_object* v___p_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile;
return v___x_610_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_compile___boxed(lean_object* v___p_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = lp_orb_x2dcompiler_Pancake_StageProg_compile(v___p_611_);
lean_dec_ref(v___p_611_);
return v_res_612_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_xfoName___closed__1(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_xfoName___closed__0));
v___x_615_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_xfoName(void){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_xfoName___closed__1, &lp_orb_x2dcompiler_Pancake_StageProg_xfoName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_xfoName___closed__1);
return v___x_616_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_xfoVal___closed__1(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_xfoVal___closed__0));
v___x_619_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_618_);
return v___x_619_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_xfoVal(void){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_xfoVal___closed__1, &lp_orb_x2dcompiler_Pancake_StageProg_xfoVal___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_xfoVal___closed__1);
return v___x_620_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_noSniffName___closed__1(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_noSniffName___closed__0));
v___x_623_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_noSniffName(void){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_noSniffName___closed__1, &lp_orb_x2dcompiler_Pancake_StageProg_noSniffName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_noSniffName___closed__1);
return v___x_624_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal___closed__1(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal___closed__0));
v___x_627_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal(void){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal___closed__1, &lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal___closed__1);
return v___x_628_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__0(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_629_ = lp_orb_x2dcompiler_Pancake_StageProg_xfoVal;
v___x_630_ = lp_orb_x2dcompiler_Pancake_StageProg_xfoName;
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___x_629_);
return v___x_631_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__1(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal;
v___x_633_ = lp_orb_x2dcompiler_Pancake_StageProg_noSniffName;
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_632_);
return v___x_634_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__2(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__1, &lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__1);
v___x_636_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__0, &lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__0);
v___x_637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_635_);
return v___x_637_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders(void){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__2, &lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders___closed__2);
return v___x_638_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_hstsName___closed__1(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_hstsName___closed__0));
v___x_641_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_hstsName(void){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_hstsName___closed__1, &lp_orb_x2dcompiler_Pancake_StageProg_hstsName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_hstsName___closed__1);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___lam__0(lean_object* v_x_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = lp_orb_x2dcompiler_Pancake_StageProg_hstsName;
return v___x_644_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___lam__0___boxed(lean_object* v_x_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___lam__0(v_x_645_);
lean_dec_ref(v_x_645_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___lam__1(lean_object* v_ctx_647_){
_start:
{
lean_object* v_cfg_648_; 
v_cfg_648_ = lean_ctor_get(v_ctx_647_, 2);
lean_inc(v_cfg_648_);
return v_cfg_648_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___lam__1___boxed(lean_object* v_ctx_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = lp_orb_x2dcompiler_Pancake_StageProg_securityHeadersCfg___lam__1(v_ctx_649_);
lean_dec_ref(v_ctx_649_);
return v_res_650_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_mGET___closed__1(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_mGET___closed__0));
v___x_659_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_mGET(void){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_mGET___closed__1, &lp_orb_x2dcompiler_Pancake_StageProg_mGET___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_mGET___closed__1);
return v___x_660_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageProg_isAllowed(lean_object* v_m_661_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_662_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_instDecidableEqReq_decEq___closed__0));
v___x_663_ = lp_orb_x2dcompiler_Pancake_StageProg_mGET;
v___x_664_ = l_instDecidableEqList___redArg(v___x_662_, v_m_661_, v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_isAllowed___boxed(lean_object* v_m_665_){
_start:
{
uint8_t v_res_666_; lean_object* v_r_667_; 
v_res_666_ = lp_orb_x2dcompiler_Pancake_StageProg_isAllowed(v_m_665_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageProg_methodFilter___lam__0(lean_object* v_ctx_668_){
_start:
{
lean_object* v_req_669_; lean_object* v_method_670_; uint8_t v___x_671_; 
v_req_669_ = lean_ctor_get(v_ctx_668_, 0);
lean_inc_ref(v_req_669_);
lean_dec_ref(v_ctx_668_);
v_method_670_ = lean_ctor_get(v_req_669_, 0);
lean_inc(v_method_670_);
lean_dec_ref(v_req_669_);
v___x_671_ = lp_orb_x2dcompiler_Pancake_StageProg_isAllowed(v_method_670_);
if (v___x_671_ == 0)
{
uint8_t v___x_672_; 
v___x_672_ = 1;
return v___x_672_;
}
else
{
uint8_t v___x_673_; 
v___x_673_ = 0;
return v___x_673_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageProg_methodFilter___lam__0___boxed(lean_object* v_ctx_674_){
_start:
{
uint8_t v_res_675_; lean_object* v_r_676_; 
v_res_675_ = lp_orb_x2dcompiler_Pancake_StageProg_methodFilter___lam__0(v_ctx_674_);
v_r_676_ = lean_box(v_res_675_);
return v_r_676_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_locationName___closed__1(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_locationName___closed__0));
v___x_684_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_683_);
return v___x_684_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_locationName(void){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_locationName___closed__1, &lp_orb_x2dcompiler_Pancake_StageProg_locationName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_locationName___closed__1);
return v___x_685_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_locationVal___closed__1(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_locationVal___closed__0));
v___x_688_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_locationVal(void){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_locationVal___closed__1, &lp_orb_x2dcompiler_Pancake_StageProg_locationVal___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_locationVal___closed__1);
return v___x_689_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_movedReason___closed__1(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_movedReason___closed__0));
v___x_692_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_movedReason(void){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_movedReason___closed__1, &lp_orb_x2dcompiler_Pancake_StageProg_movedReason___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_movedReason___closed__1);
return v___x_693_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__0(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lp_orb_x2dcompiler_Pancake_StageProg_movedReason;
v___x_695_ = lean_unsigned_to_nat(308u);
v___x_696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_694_);
return v___x_696_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__3(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lp_orb_x2dcompiler_Pancake_StageProg_locationVal;
v___x_702_ = lp_orb_x2dcompiler_Pancake_StageProg_locationName;
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v___x_701_);
return v___x_703_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__4(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__3, &lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__3);
v___x_705_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__2));
v___x_706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v___x_704_);
return v___x_706_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__5(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__4, &lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__4);
v___x_708_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__0, &lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__0);
v___x_709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___x_707_);
return v___x_709_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_redirect(void){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__5, &lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_redirect___closed__5);
return v___x_710_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__1(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__0));
v___x_713_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_712_);
return v___x_713_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__2(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__1, &lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__1);
v___x_715_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200(v___x_714_);
return v___x_715_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_baseOk(void){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__2, &lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_baseOk___closed__2);
return v___x_716_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__0(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_box(0);
v___x_718_ = lp_orb_x2dcompiler_Pancake_StageProg_mGET;
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v___x_717_);
return v___x_719_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__2(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__1));
v___x_722_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_721_);
return v___x_722_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__3(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_723_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__2, &lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__2);
v___x_724_ = lp_orb_x2dcompiler_Pancake_StageProg_baseOk;
v___x_725_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__0, &lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__0);
v___x_726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v___x_724_);
lean_ctor_set(v___x_726_, 2, v___x_723_);
return v___x_726_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxGet(void){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__3, &lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__3);
return v___x_727_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__1(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__0));
v___x_730_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_729_);
return v___x_730_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__2(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_box(0);
v___x_732_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__1, &lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__1);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___x_731_);
return v___x_733_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__3(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_734_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__2, &lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__2);
v___x_735_ = lp_orb_x2dcompiler_Pancake_StageProg_baseOk;
v___x_736_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__2, &lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__2);
v___x_737_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v___x_735_);
lean_ctor_set(v___x_737_, 2, v___x_734_);
return v___x_737_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxPost(void){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__3, &lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxPost___closed__3);
return v___x_738_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_cfgA___closed__1(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_cfgA___closed__0));
v___x_741_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_740_);
return v___x_741_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_cfgA(void){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_cfgA___closed__1, &lp_orb_x2dcompiler_Pancake_StageProg_cfgA___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_cfgA___closed__1);
return v___x_742_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_cfgB___closed__1(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageProg_cfgB___closed__0));
v___x_745_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_cfgB(void){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_cfgB___closed__1, &lp_orb_x2dcompiler_Pancake_StageProg_cfgB___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_cfgB___closed__1);
return v___x_746_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgA___closed__0(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_747_ = lp_orb_x2dcompiler_Pancake_StageProg_cfgA;
v___x_748_ = lp_orb_x2dcompiler_Pancake_StageProg_baseOk;
v___x_749_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__0, &lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__0);
v___x_750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v___x_748_);
lean_ctor_set(v___x_750_, 2, v___x_747_);
return v___x_750_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgA(void){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgA___closed__0, &lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgA___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgA___closed__0);
return v___x_751_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgB___closed__0(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_752_ = lp_orb_x2dcompiler_Pancake_StageProg_cfgB;
v___x_753_ = lp_orb_x2dcompiler_Pancake_StageProg_baseOk;
v___x_754_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__0, &lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxGet___closed__0);
v___x_755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v___x_753_);
lean_ctor_set(v___x_755_, 2, v___x_752_);
return v___x_755_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgB(void){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgB___closed__0, &lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgB___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgB___closed__0);
return v___x_756_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_SerializeCompile(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_StageProg(uint8_t builtin) {
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
lp_orb_x2dcompiler_Pancake_StageProg_xfoName = _init_lp_orb_x2dcompiler_Pancake_StageProg_xfoName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_xfoName);
lp_orb_x2dcompiler_Pancake_StageProg_xfoVal = _init_lp_orb_x2dcompiler_Pancake_StageProg_xfoVal();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_xfoVal);
lp_orb_x2dcompiler_Pancake_StageProg_noSniffName = _init_lp_orb_x2dcompiler_Pancake_StageProg_noSniffName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_noSniffName);
lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal = _init_lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_noSniffVal);
lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders = _init_lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_securityHeaders);
lp_orb_x2dcompiler_Pancake_StageProg_hstsName = _init_lp_orb_x2dcompiler_Pancake_StageProg_hstsName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_hstsName);
lp_orb_x2dcompiler_Pancake_StageProg_mGET = _init_lp_orb_x2dcompiler_Pancake_StageProg_mGET();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_mGET);
lp_orb_x2dcompiler_Pancake_StageProg_locationName = _init_lp_orb_x2dcompiler_Pancake_StageProg_locationName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_locationName);
lp_orb_x2dcompiler_Pancake_StageProg_locationVal = _init_lp_orb_x2dcompiler_Pancake_StageProg_locationVal();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_locationVal);
lp_orb_x2dcompiler_Pancake_StageProg_movedReason = _init_lp_orb_x2dcompiler_Pancake_StageProg_movedReason();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_movedReason);
lp_orb_x2dcompiler_Pancake_StageProg_redirect = _init_lp_orb_x2dcompiler_Pancake_StageProg_redirect();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_redirect);
lp_orb_x2dcompiler_Pancake_StageProg_baseOk = _init_lp_orb_x2dcompiler_Pancake_StageProg_baseOk();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_baseOk);
lp_orb_x2dcompiler_Pancake_StageProg_ctxGet = _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxGet();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_ctxGet);
lp_orb_x2dcompiler_Pancake_StageProg_ctxPost = _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxPost();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_ctxPost);
lp_orb_x2dcompiler_Pancake_StageProg_cfgA = _init_lp_orb_x2dcompiler_Pancake_StageProg_cfgA();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_cfgA);
lp_orb_x2dcompiler_Pancake_StageProg_cfgB = _init_lp_orb_x2dcompiler_Pancake_StageProg_cfgB();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_cfgB);
lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgA = _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgA();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgA);
lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgB = _init_lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgB();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageProg_ctxCfgB);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
