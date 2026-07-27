// Lean compiler output
// Module: Pancake.PredEval
// Imports: public import Init public meta import Init public import Pancake.StageCompile
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
lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_StageProg_str(lean_object*);
extern lean_object* lp_orb_x2dcompiler_Pancake_StageProg_baseOk;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_instDecidableEqBitVec___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instDecidableEqBitVec___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(8) << 1) | 1))} };
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__2;
static const lean_string_object lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__3_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__4;
static const lean_string_object lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__5_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__6;
static const lean_string_object lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__7_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__8;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_methodTag(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_methodLt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_methodLt_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_methodGe_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_methodGe_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_methodIn_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_methodIn_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_always_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_always_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_never_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_never_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__2_value;
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__5_value;
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__8;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__10_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Pancake.PredEval.PredSpec.always"};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Pancake.PredEval.PredSpec.never"};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Pancake.PredEval.PredSpec.methodLt"};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__4_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__6_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8;
static const lean_string_object lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Pancake.PredEval.PredSpec.methodGe"};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__9_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__10_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__11_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Pancake.PredEval.PredSpec.methodIn"};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__12_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__12_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__13_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__14_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec___closed__0_value;
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq___closed__0_value;
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_PredEval_denotePred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instBEqOfDecidableEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__0_value)} };
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_denotePred___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_denotePred___closed__0_value;
static const lean_closure_object lp_orb_x2dcompiler_Pancake_PredEval_denotePred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_beq___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_denotePred___closed__0_value)} };
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_denotePred___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_denotePred___closed__1_value;
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_PredEval_denotePred(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_denotePred___boxed(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__2;
static const lean_string_object lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "max-age=31536000; includeSubDomains; preload"};
static const lean_object* lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__3_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__5;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_ctxPut;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__3;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_predEval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_PredEval_0__Pancake_PredEval_denotePred_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_PredEval_0__Pancake_PredEval_denotePred_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_methodFilterGate(lean_object*);
static lean_object* _init_lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__1));
v___x_5_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__4(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__3));
v___x_8_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__6(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__5));
v___x_11_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__8(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__7));
v___x_14_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_methodTag(lean_object* v_m_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_16_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__0));
v___x_17_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__2, &lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__2);
lean_inc(v_m_15_);
v___x_18_ = l_instDecidableEqList___redArg(v___x_16_, v_m_15_, v___x_17_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_19_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__4, &lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__4);
lean_inc(v_m_15_);
v___x_20_ = l_instDecidableEqList___redArg(v___x_16_, v_m_15_, v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_21_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__6, &lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__6);
lean_inc(v_m_15_);
v___x_22_ = l_instDecidableEqList___redArg(v___x_16_, v_m_15_, v___x_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_23_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__8, &lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__8);
v___x_24_ = l_instDecidableEqList___redArg(v___x_16_, v_m_15_, v___x_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; 
v___x_25_ = lean_unsigned_to_nat(4u);
return v___x_25_;
}
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_unsigned_to_nat(3u);
return v___x_26_;
}
}
else
{
lean_object* v___x_27_; 
lean_dec(v_m_15_);
v___x_27_ = lean_unsigned_to_nat(2u);
return v___x_27_;
}
}
else
{
lean_object* v___x_28_; 
lean_dec(v_m_15_);
v___x_28_ = lean_unsigned_to_nat(1u);
return v___x_28_;
}
}
else
{
lean_object* v___x_29_; 
lean_dec(v_m_15_);
v___x_29_ = lean_unsigned_to_nat(0u);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorIdx(lean_object* v_x_30_){
_start:
{
switch(lean_obj_tag(v_x_30_))
{
case 0:
{
lean_object* v___x_31_; 
v___x_31_ = lean_unsigned_to_nat(0u);
return v___x_31_;
}
case 1:
{
lean_object* v___x_32_; 
v___x_32_ = lean_unsigned_to_nat(1u);
return v___x_32_;
}
case 2:
{
lean_object* v___x_33_; 
v___x_33_ = lean_unsigned_to_nat(2u);
return v___x_33_;
}
case 3:
{
lean_object* v___x_34_; 
v___x_34_ = lean_unsigned_to_nat(3u);
return v___x_34_;
}
default: 
{
lean_object* v___x_35_; 
v___x_35_ = lean_unsigned_to_nat(4u);
return v___x_35_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorIdx___boxed(lean_object* v_x_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorIdx(v_x_36_);
lean_dec(v_x_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim___redArg(lean_object* v_t_38_, lean_object* v_k_39_){
_start:
{
switch(lean_obj_tag(v_t_38_))
{
case 0:
{
lean_object* v_bound_40_; lean_object* v___x_41_; 
v_bound_40_ = lean_ctor_get(v_t_38_, 0);
lean_inc(v_bound_40_);
lean_dec_ref(v_t_38_);
v___x_41_ = lean_apply_1(v_k_39_, v_bound_40_);
return v___x_41_;
}
case 1:
{
lean_object* v_bound_42_; lean_object* v___x_43_; 
v_bound_42_ = lean_ctor_get(v_t_38_, 0);
lean_inc(v_bound_42_);
lean_dec_ref(v_t_38_);
v___x_43_ = lean_apply_1(v_k_39_, v_bound_42_);
return v___x_43_;
}
case 2:
{
lean_object* v_methods_44_; lean_object* v___x_45_; 
v_methods_44_ = lean_ctor_get(v_t_38_, 0);
lean_inc(v_methods_44_);
lean_dec_ref(v_t_38_);
v___x_45_ = lean_apply_1(v_k_39_, v_methods_44_);
return v___x_45_;
}
default: 
{
lean_dec(v_t_38_);
return v_k_39_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim(lean_object* v_motive_46_, lean_object* v_ctorIdx_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_k_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim___redArg(v_t_48_, v_k_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim___boxed(lean_object* v_motive_52_, lean_object* v_ctorIdx_53_, lean_object* v_t_54_, lean_object* v_h_55_, lean_object* v_k_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim(v_motive_52_, v_ctorIdx_53_, v_t_54_, v_h_55_, v_k_56_);
lean_dec(v_ctorIdx_53_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_methodLt_elim___redArg(lean_object* v_t_58_, lean_object* v_methodLt_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim___redArg(v_t_58_, v_methodLt_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_methodLt_elim(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_methodLt_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim___redArg(v_t_62_, v_methodLt_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_methodGe_elim___redArg(lean_object* v_t_66_, lean_object* v_methodGe_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim___redArg(v_t_66_, v_methodGe_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_methodGe_elim(lean_object* v_motive_69_, lean_object* v_t_70_, lean_object* v_h_71_, lean_object* v_methodGe_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim___redArg(v_t_70_, v_methodGe_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_methodIn_elim___redArg(lean_object* v_t_74_, lean_object* v_methodIn_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim___redArg(v_t_74_, v_methodIn_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_methodIn_elim(lean_object* v_motive_77_, lean_object* v_t_78_, lean_object* v_h_79_, lean_object* v_methodIn_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim___redArg(v_t_78_, v_methodIn_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_always_elim___redArg(lean_object* v_t_82_, lean_object* v_always_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim___redArg(v_t_82_, v_always_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_always_elim(lean_object* v_motive_85_, lean_object* v_t_86_, lean_object* v_h_87_, lean_object* v_always_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim___redArg(v_t_86_, v_always_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_never_elim___redArg(lean_object* v_t_90_, lean_object* v_never_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim___redArg(v_t_90_, v_never_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_never_elim(lean_object* v_motive_93_, lean_object* v_t_94_, lean_object* v_h_95_, lean_object* v_never_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lp_orb_x2dcompiler_Pancake_PredEval_PredSpec_ctorElim___redArg(v_t_94_, v_never_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_98_, lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
if (lean_obj_tag(v_x_100_) == 0)
{
lean_dec(v_x_98_);
return v_x_99_;
}
else
{
lean_object* v_head_101_; lean_object* v_tail_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_112_; 
v_head_101_ = lean_ctor_get(v_x_100_, 0);
v_tail_102_ = lean_ctor_get(v_x_100_, 1);
v_isSharedCheck_112_ = !lean_is_exclusive(v_x_100_);
if (v_isSharedCheck_112_ == 0)
{
v___x_104_ = v_x_100_;
v_isShared_105_ = v_isSharedCheck_112_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_tail_102_);
lean_inc(v_head_101_);
lean_dec(v_x_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_112_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
lean_inc(v_x_98_);
if (v_isShared_105_ == 0)
{
lean_ctor_set_tag(v___x_104_, 5);
lean_ctor_set(v___x_104_, 1, v_x_98_);
lean_ctor_set(v___x_104_, 0, v_x_99_);
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_x_99_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_x_98_);
v___x_107_ = v_reuseFailAlloc_111_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg(v_head_101_);
v___x_109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_107_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v_x_99_ = v___x_109_;
v_x_100_ = v_tail_102_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0_spec__0_spec__1(lean_object* v_x_113_, lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
if (lean_obj_tag(v_x_115_) == 0)
{
lean_dec(v_x_113_);
return v_x_114_;
}
else
{
lean_object* v_head_116_; lean_object* v_tail_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_127_; 
v_head_116_ = lean_ctor_get(v_x_115_, 0);
v_tail_117_ = lean_ctor_get(v_x_115_, 1);
v_isSharedCheck_127_ = !lean_is_exclusive(v_x_115_);
if (v_isSharedCheck_127_ == 0)
{
v___x_119_ = v_x_115_;
v_isShared_120_ = v_isSharedCheck_127_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_tail_117_);
lean_inc(v_head_116_);
lean_dec(v_x_115_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_127_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
lean_inc(v_x_113_);
if (v_isShared_120_ == 0)
{
lean_ctor_set_tag(v___x_119_, 5);
lean_ctor_set(v___x_119_, 1, v_x_113_);
lean_ctor_set(v___x_119_, 0, v_x_114_);
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_x_114_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_x_113_);
v___x_122_ = v_reuseFailAlloc_126_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_123_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg(v_head_116_);
v___x_124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_122_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = lp_orb_x2dcompiler_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0_spec__0_spec__1_spec__2(v_x_113_, v___x_124_, v_tail_117_);
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0_spec__0(lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_object* v___x_130_; 
lean_dec(v_x_129_);
v___x_130_ = lean_box(0);
return v___x_130_;
}
else
{
lean_object* v_tail_131_; 
v_tail_131_ = lean_ctor_get(v_x_128_, 1);
if (lean_obj_tag(v_tail_131_) == 0)
{
lean_object* v_head_132_; lean_object* v___x_133_; 
lean_dec(v_x_129_);
v_head_132_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_head_132_);
lean_dec_ref(v_x_128_);
v___x_133_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg(v_head_132_);
return v___x_133_;
}
else
{
lean_object* v_head_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
lean_inc(v_tail_131_);
v_head_134_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_head_134_);
lean_dec_ref(v_x_128_);
v___x_135_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_StageProg_instReprReq_repr_spec__0___redArg(v_head_134_);
v___x_136_ = lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0_spec__0_spec__1(v_x_129_, v___x_135_, v_tail_131_);
return v___x_136_;
}
}
}
}
static lean_object* _init_lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__2));
v___x_149_ = lean_string_length(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_obj_once(&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__7, &lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__7_once, _init_lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__7);
v___x_151_ = lean_nat_to_int(v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg(lean_object* v_a_156_){
_start:
{
if (lean_obj_tag(v_a_156_) == 0)
{
lean_object* v___x_157_; 
v___x_157_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__1));
return v___x_157_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; 
v___x_158_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__5));
v___x_159_ = lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0_spec__0(v_a_156_, v___x_158_);
v___x_160_ = lean_obj_once(&lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__8, &lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__8_once, _init_lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__8);
v___x_161_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__9));
v___x_162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_159_);
v___x_163_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg___closed__10));
v___x_164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_160_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = 0;
v___x_167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*1, v___x_166_);
return v___x_167_;
}
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(2u);
v___x_181_ = lean_nat_to_int(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_nat_to_int(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr(lean_object* v_x_196_, lean_object* v_prec_197_){
_start:
{
lean_object* v___y_199_; lean_object* v___y_206_; 
switch(lean_obj_tag(v_x_196_))
{
case 0:
{
lean_object* v_bound_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_232_; 
v_bound_212_ = lean_ctor_get(v_x_196_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v_x_196_);
if (v_isSharedCheck_232_ == 0)
{
v___x_214_ = v_x_196_;
v_isShared_215_ = v_isSharedCheck_232_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_bound_212_);
lean_dec(v_x_196_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_232_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___y_217_; lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_228_ = lean_unsigned_to_nat(1024u);
v___x_229_ = lean_nat_dec_le(v___x_228_, v_prec_197_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
v___x_230_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7, &lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7);
v___y_217_ = v___x_230_;
goto v___jp_216_;
}
else
{
lean_object* v___x_231_; 
v___x_231_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8, &lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8);
v___y_217_ = v___x_231_;
goto v___jp_216_;
}
v___jp_216_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_218_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__6));
v___x_219_ = l_Nat_reprFast(v_bound_212_);
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 3);
lean_ctor_set(v___x_214_, 0, v___x_219_);
v___x_221_ = v___x_214_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_227_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_218_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
lean_inc(v___y_217_);
v___x_223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_223_, 0, v___y_217_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = 0;
v___x_225_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_224_);
v___x_226_ = l_Repr_addAppParen(v___x_225_, v_prec_197_);
return v___x_226_;
}
}
}
}
case 1:
{
lean_object* v_bound_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_253_; 
v_bound_233_ = lean_ctor_get(v_x_196_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_196_);
if (v_isSharedCheck_253_ == 0)
{
v___x_235_ = v_x_196_;
v_isShared_236_ = v_isSharedCheck_253_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_bound_233_);
lean_dec(v_x_196_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_253_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___y_238_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_unsigned_to_nat(1024u);
v___x_250_ = lean_nat_dec_le(v___x_249_, v_prec_197_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
v___x_251_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7, &lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7);
v___y_238_ = v___x_251_;
goto v___jp_237_;
}
else
{
lean_object* v___x_252_; 
v___x_252_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8, &lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8);
v___y_238_ = v___x_252_;
goto v___jp_237_;
}
v___jp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_239_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__11));
v___x_240_ = l_Nat_reprFast(v_bound_233_);
if (v_isShared_236_ == 0)
{
lean_ctor_set_tag(v___x_235_, 3);
lean_ctor_set(v___x_235_, 0, v___x_240_);
v___x_242_ = v___x_235_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_248_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_239_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
lean_inc(v___y_238_);
v___x_244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_244_, 0, v___y_238_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = 0;
v___x_246_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*1, v___x_245_);
v___x_247_ = l_Repr_addAppParen(v___x_246_, v_prec_197_);
return v___x_247_;
}
}
}
}
case 2:
{
lean_object* v_methods_254_; lean_object* v___y_256_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_methods_254_ = lean_ctor_get(v_x_196_, 0);
lean_inc(v_methods_254_);
lean_dec_ref(v_x_196_);
v___x_264_ = lean_unsigned_to_nat(1024u);
v___x_265_ = lean_nat_dec_le(v___x_264_, v_prec_197_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
v___x_266_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7, &lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7);
v___y_256_ = v___x_266_;
goto v___jp_255_;
}
else
{
lean_object* v___x_267_; 
v___x_267_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8, &lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8);
v___y_256_ = v___x_267_;
goto v___jp_255_;
}
v___jp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_257_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__14));
v___x_258_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg(v_methods_254_);
v___x_259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
lean_inc(v___y_256_);
v___x_260_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_260_, 0, v___y_256_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = 0;
v___x_262_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*1, v___x_261_);
v___x_263_ = l_Repr_addAppParen(v___x_262_, v_prec_197_);
return v___x_263_;
}
}
case 3:
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(1024u);
v___x_269_ = lean_nat_dec_le(v___x_268_, v_prec_197_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7, &lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7);
v___y_199_ = v___x_270_;
goto v___jp_198_;
}
else
{
lean_object* v___x_271_; 
v___x_271_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8, &lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8);
v___y_199_ = v___x_271_;
goto v___jp_198_;
}
}
default: 
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = lean_unsigned_to_nat(1024u);
v___x_273_ = lean_nat_dec_le(v___x_272_, v_prec_197_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7, &lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__7);
v___y_206_ = v___x_274_;
goto v___jp_205_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8, &lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__8);
v___y_206_ = v___x_275_;
goto v___jp_205_;
}
}
}
v___jp_198_:
{
lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_200_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__1));
lean_inc(v___y_199_);
v___x_201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_201_, 0, v___y_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = 0;
v___x_203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*1, v___x_202_);
v___x_204_ = l_Repr_addAppParen(v___x_203_, v_prec_197_);
return v___x_204_;
}
v___jp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_207_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___closed__3));
lean_inc(v___y_206_);
v___x_208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_208_, 0, v___y_206_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = 0;
v___x_210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*1, v___x_209_);
v___x_211_ = l_Repr_addAppParen(v___x_210_, v_prec_197_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr___boxed(lean_object* v_x_276_, lean_object* v_prec_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = lp_orb_x2dcompiler_Pancake_PredEval_instReprPredSpec_repr(v_x_276_, v_prec_277_);
lean_dec(v_prec_277_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0(lean_object* v_a_279_, lean_object* v_n_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___redArg(v_a_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0___boxed(lean_object* v_a_282_, lean_object* v_n_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_PredEval_instReprPredSpec_repr_spec__0(v_a_282_, v_n_283_);
lean_dec(v_n_283_);
return v_res_284_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq___lam__0(lean_object* v_a_287_, lean_object* v_b_288_){
_start:
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PredEval_methodTag___closed__0));
v___x_290_ = l_instDecidableEqList___redArg(v___x_289_, v_a_287_, v_b_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq___lam__0___boxed(lean_object* v_a_291_, lean_object* v_b_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq___lam__0(v_a_291_, v_b_292_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq(lean_object* v_x_296_, lean_object* v_x_297_){
_start:
{
switch(lean_obj_tag(v_x_296_))
{
case 0:
{
lean_object* v_bound_298_; uint8_t v___x_299_; 
v_bound_298_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_bound_298_);
lean_dec_ref(v_x_296_);
v___x_299_ = 0;
switch(lean_obj_tag(v_x_297_))
{
case 0:
{
lean_object* v_bound_300_; uint8_t v___x_301_; 
v_bound_300_ = lean_ctor_get(v_x_297_, 0);
lean_inc(v_bound_300_);
lean_dec_ref(v_x_297_);
v___x_301_ = lean_nat_dec_eq(v_bound_298_, v_bound_300_);
lean_dec(v_bound_300_);
lean_dec(v_bound_298_);
if (v___x_301_ == 0)
{
return v___x_299_;
}
else
{
return v___x_301_;
}
}
case 3:
{
lean_dec(v_bound_298_);
return v___x_299_;
}
case 4:
{
lean_dec(v_bound_298_);
return v___x_299_;
}
default: 
{
lean_dec(v_bound_298_);
lean_dec(v_x_297_);
return v___x_299_;
}
}
}
case 1:
{
lean_object* v_bound_302_; uint8_t v___x_303_; 
v_bound_302_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_bound_302_);
lean_dec_ref(v_x_296_);
v___x_303_ = 0;
switch(lean_obj_tag(v_x_297_))
{
case 1:
{
lean_object* v_bound_304_; uint8_t v___x_305_; 
v_bound_304_ = lean_ctor_get(v_x_297_, 0);
lean_inc(v_bound_304_);
lean_dec_ref(v_x_297_);
v___x_305_ = lean_nat_dec_eq(v_bound_302_, v_bound_304_);
lean_dec(v_bound_304_);
lean_dec(v_bound_302_);
if (v___x_305_ == 0)
{
return v___x_303_;
}
else
{
return v___x_305_;
}
}
case 3:
{
lean_dec(v_bound_302_);
return v___x_303_;
}
case 4:
{
lean_dec(v_bound_302_);
return v___x_303_;
}
default: 
{
lean_dec(v_bound_302_);
lean_dec(v_x_297_);
return v___x_303_;
}
}
}
case 2:
{
lean_object* v_methods_306_; uint8_t v___x_307_; 
v_methods_306_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_methods_306_);
lean_dec_ref(v_x_296_);
v___x_307_ = 0;
switch(lean_obj_tag(v_x_297_))
{
case 2:
{
lean_object* v_methods_308_; lean_object* v___f_309_; uint8_t v___x_310_; 
v_methods_308_ = lean_ctor_get(v_x_297_, 0);
lean_inc(v_methods_308_);
lean_dec_ref(v_x_297_);
v___f_309_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq___closed__0));
v___x_310_ = l_instDecidableEqList___redArg(v___f_309_, v_methods_306_, v_methods_308_);
if (v___x_310_ == 0)
{
return v___x_307_;
}
else
{
return v___x_310_;
}
}
case 3:
{
lean_dec(v_methods_306_);
return v___x_307_;
}
case 4:
{
lean_dec(v_methods_306_);
return v___x_307_;
}
default: 
{
lean_dec(v_methods_306_);
lean_dec(v_x_297_);
return v___x_307_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_297_))
{
case 3:
{
uint8_t v___x_311_; 
v___x_311_ = 1;
return v___x_311_;
}
case 4:
{
uint8_t v___x_312_; 
v___x_312_ = 0;
return v___x_312_;
}
default: 
{
uint8_t v___x_313_; 
lean_dec(v_x_297_);
v___x_313_ = 0;
return v___x_313_;
}
}
}
default: 
{
switch(lean_obj_tag(v_x_297_))
{
case 3:
{
uint8_t v___x_314_; 
v___x_314_ = 0;
return v___x_314_;
}
case 4:
{
uint8_t v___x_315_; 
v___x_315_ = 1;
return v___x_315_;
}
default: 
{
uint8_t v___x_316_; 
lean_dec(v_x_297_);
v___x_316_ = 0;
return v___x_316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq___boxed(lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq(v_x_317_, v_x_318_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec(lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
uint8_t v___x_323_; 
v___x_323_ = lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec_decEq(v_x_321_, v_x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec___boxed(lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = lp_orb_x2dcompiler_Pancake_PredEval_instDecidableEqPredSpec(v_x_324_, v_x_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_PredEval_denotePred(lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
switch(lean_obj_tag(v_x_332_))
{
case 0:
{
lean_object* v_req_334_; lean_object* v_bound_335_; lean_object* v_method_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_req_334_ = lean_ctor_get(v_x_333_, 0);
lean_inc_ref(v_req_334_);
lean_dec_ref(v_x_333_);
v_bound_335_ = lean_ctor_get(v_x_332_, 0);
lean_inc(v_bound_335_);
lean_dec_ref(v_x_332_);
v_method_336_ = lean_ctor_get(v_req_334_, 0);
lean_inc(v_method_336_);
lean_dec_ref(v_req_334_);
v___x_337_ = lp_orb_x2dcompiler_Pancake_PredEval_methodTag(v_method_336_);
v___x_338_ = lean_nat_dec_lt(v___x_337_, v_bound_335_);
lean_dec(v_bound_335_);
lean_dec(v___x_337_);
return v___x_338_;
}
case 1:
{
lean_object* v_req_339_; lean_object* v_bound_340_; lean_object* v_method_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_req_339_ = lean_ctor_get(v_x_333_, 0);
lean_inc_ref(v_req_339_);
lean_dec_ref(v_x_333_);
v_bound_340_ = lean_ctor_get(v_x_332_, 0);
lean_inc(v_bound_340_);
lean_dec_ref(v_x_332_);
v_method_341_ = lean_ctor_get(v_req_339_, 0);
lean_inc(v_method_341_);
lean_dec_ref(v_req_339_);
v___x_342_ = lp_orb_x2dcompiler_Pancake_PredEval_methodTag(v_method_341_);
v___x_343_ = lean_nat_dec_le(v_bound_340_, v___x_342_);
lean_dec(v___x_342_);
lean_dec(v_bound_340_);
return v___x_343_;
}
case 2:
{
lean_object* v_req_344_; lean_object* v_methods_345_; lean_object* v_method_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_req_344_ = lean_ctor_get(v_x_333_, 0);
lean_inc_ref(v_req_344_);
lean_dec_ref(v_x_333_);
v_methods_345_ = lean_ctor_get(v_x_332_, 0);
lean_inc(v_methods_345_);
lean_dec_ref(v_x_332_);
v_method_346_ = lean_ctor_get(v_req_344_, 0);
lean_inc(v_method_346_);
lean_dec_ref(v_req_344_);
v___x_347_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PredEval_denotePred___closed__1));
v___x_348_ = l_List_elem___redArg(v___x_347_, v_method_346_, v_methods_345_);
return v___x_348_;
}
case 3:
{
uint8_t v___x_349_; 
lean_dec_ref(v_x_333_);
v___x_349_ = 1;
return v___x_349_;
}
default: 
{
uint8_t v___x_350_; 
lean_dec_ref(v_x_333_);
v___x_350_ = 0;
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_denotePred___boxed(lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = lp_orb_x2dcompiler_Pancake_PredEval_denotePred(v_x_351_, v_x_352_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__1(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__0));
v___x_357_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__2(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = lean_box(0);
v___x_359_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__1, &lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__1);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___x_358_);
return v___x_360_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__4(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__3));
v___x_363_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__5(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_364_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__4, &lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__4);
v___x_365_ = lp_orb_x2dcompiler_Pancake_StageProg_baseOk;
v___x_366_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__2, &lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__2);
v___x_367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v___x_365_);
lean_ctor_set(v___x_367_, 2, v___x_364_);
return v___x_367_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_PredEval_ctxPut(void){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__5, &lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_ctxPut___closed__5);
return v___x_368_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__0(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_unsigned_to_nat(64u);
v___x_371_ = l_BitVec_ofNat(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__1(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__0, &lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__0);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__2(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_unsigned_to_nat(64u);
v___x_376_ = l_BitVec_ofNat(v___x_375_, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__3(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__2, &lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__2);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_predEval(lean_object* v_aMethod_379_, lean_object* v_name_380_, lean_object* v_x_381_){
_start:
{
switch(lean_obj_tag(v_x_381_))
{
case 0:
{
lean_object* v_bound_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_396_; 
v_bound_382_ = lean_ctor_get(v_x_381_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_396_ == 0)
{
v___x_384_ = v_x_381_;
v_isShared_385_ = v_isSharedCheck_396_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_bound_382_);
lean_dec(v_x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_396_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
uint8_t v___x_386_; lean_object* v___x_388_; 
v___x_386_ = 0;
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v_aMethod_379_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_aMethod_379_);
v___x_388_ = v_reuseFailAlloc_395_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_389_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
v___x_390_ = lean_unsigned_to_nat(64u);
v___x_391_ = l_BitVec_ofNat(v___x_390_, v_bound_382_);
lean_dec(v_bound_382_);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
v___x_393_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_393_, 0, v___x_389_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*2, v___x_386_);
v___x_394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_394_, 0, v_name_380_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
return v___x_394_;
}
}
}
case 1:
{
lean_object* v_bound_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_411_; 
v_bound_397_ = lean_ctor_get(v_x_381_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_411_ == 0)
{
v___x_399_ = v_x_381_;
v_isShared_400_ = v_isSharedCheck_411_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_bound_397_);
lean_dec(v_x_381_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_411_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
uint8_t v___x_401_; lean_object* v___x_403_; 
v___x_401_ = 2;
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 0);
lean_ctor_set(v___x_399_, 0, v_aMethod_379_);
v___x_403_ = v___x_399_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_aMethod_379_);
v___x_403_ = v_reuseFailAlloc_410_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_404_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
v___x_405_ = lean_unsigned_to_nat(64u);
v___x_406_ = l_BitVec_ofNat(v___x_405_, v_bound_397_);
lean_dec(v_bound_397_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
v___x_408_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_408_, 0, v___x_404_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*2, v___x_401_);
v___x_409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_409_, 0, v_name_380_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
return v___x_409_;
}
}
}
case 3:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
lean_dec(v_aMethod_379_);
v___x_412_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__1, &lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__1);
v___x_413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_413_, 0, v_name_380_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
return v___x_413_;
}
default: 
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec(v_x_381_);
lean_dec(v_aMethod_379_);
v___x_414_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__3, &lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_PredEval_predEval___closed__3);
v___x_415_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_415_, 0, v_name_380_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
return v___x_415_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_PredEval_0__Pancake_PredEval_denotePred_match__1_splitter___redArg(lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v_h__1_418_, lean_object* v_h__2_419_, lean_object* v_h__3_420_, lean_object* v_h__4_421_, lean_object* v_h__5_422_){
_start:
{
switch(lean_obj_tag(v_x_416_))
{
case 0:
{
lean_object* v_bound_423_; lean_object* v___x_424_; 
lean_dec(v_h__5_422_);
lean_dec(v_h__4_421_);
lean_dec(v_h__3_420_);
lean_dec(v_h__2_419_);
v_bound_423_ = lean_ctor_get(v_x_416_, 0);
lean_inc(v_bound_423_);
lean_dec_ref(v_x_416_);
v___x_424_ = lean_apply_2(v_h__1_418_, v_bound_423_, v_x_417_);
return v___x_424_;
}
case 1:
{
lean_object* v_bound_425_; lean_object* v___x_426_; 
lean_dec(v_h__5_422_);
lean_dec(v_h__4_421_);
lean_dec(v_h__3_420_);
lean_dec(v_h__1_418_);
v_bound_425_ = lean_ctor_get(v_x_416_, 0);
lean_inc(v_bound_425_);
lean_dec_ref(v_x_416_);
v___x_426_ = lean_apply_2(v_h__2_419_, v_bound_425_, v_x_417_);
return v___x_426_;
}
case 2:
{
lean_object* v_methods_427_; lean_object* v___x_428_; 
lean_dec(v_h__5_422_);
lean_dec(v_h__4_421_);
lean_dec(v_h__2_419_);
lean_dec(v_h__1_418_);
v_methods_427_ = lean_ctor_get(v_x_416_, 0);
lean_inc(v_methods_427_);
lean_dec_ref(v_x_416_);
v___x_428_ = lean_apply_2(v_h__3_420_, v_methods_427_, v_x_417_);
return v___x_428_;
}
case 3:
{
lean_object* v___x_429_; 
lean_dec(v_h__5_422_);
lean_dec(v_h__3_420_);
lean_dec(v_h__2_419_);
lean_dec(v_h__1_418_);
v___x_429_ = lean_apply_1(v_h__4_421_, v_x_417_);
return v___x_429_;
}
default: 
{
lean_object* v___x_430_; 
lean_dec(v_h__4_421_);
lean_dec(v_h__3_420_);
lean_dec(v_h__2_419_);
lean_dec(v_h__1_418_);
v___x_430_ = lean_apply_1(v_h__5_422_, v_x_417_);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_PredEval_0__Pancake_PredEval_denotePred_match__1_splitter(lean_object* v_motive_431_, lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_h__1_434_, lean_object* v_h__2_435_, lean_object* v_h__3_436_, lean_object* v_h__4_437_, lean_object* v_h__5_438_){
_start:
{
switch(lean_obj_tag(v_x_432_))
{
case 0:
{
lean_object* v_bound_439_; lean_object* v___x_440_; 
lean_dec(v_h__5_438_);
lean_dec(v_h__4_437_);
lean_dec(v_h__3_436_);
lean_dec(v_h__2_435_);
v_bound_439_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_bound_439_);
lean_dec_ref(v_x_432_);
v___x_440_ = lean_apply_2(v_h__1_434_, v_bound_439_, v_x_433_);
return v___x_440_;
}
case 1:
{
lean_object* v_bound_441_; lean_object* v___x_442_; 
lean_dec(v_h__5_438_);
lean_dec(v_h__4_437_);
lean_dec(v_h__3_436_);
lean_dec(v_h__1_434_);
v_bound_441_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_bound_441_);
lean_dec_ref(v_x_432_);
v___x_442_ = lean_apply_2(v_h__2_435_, v_bound_441_, v_x_433_);
return v___x_442_;
}
case 2:
{
lean_object* v_methods_443_; lean_object* v___x_444_; 
lean_dec(v_h__5_438_);
lean_dec(v_h__4_437_);
lean_dec(v_h__2_435_);
lean_dec(v_h__1_434_);
v_methods_443_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_methods_443_);
lean_dec_ref(v_x_432_);
v___x_444_ = lean_apply_2(v_h__3_436_, v_methods_443_, v_x_433_);
return v___x_444_;
}
case 3:
{
lean_object* v___x_445_; 
lean_dec(v_h__5_438_);
lean_dec(v_h__3_436_);
lean_dec(v_h__2_435_);
lean_dec(v_h__1_434_);
v___x_445_ = lean_apply_1(v_h__4_437_, v_x_433_);
return v___x_445_;
}
default: 
{
lean_object* v___x_446_; 
lean_dec(v_h__4_437_);
lean_dec(v_h__3_436_);
lean_dec(v_h__2_435_);
lean_dec(v_h__1_434_);
v___x_446_ = lean_apply_1(v_h__5_438_, v_x_433_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_PredEval_methodFilterGate(lean_object* v_b_447_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v_b_447_);
v___x_449_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_PredEval_denotePred___boxed), 2, 1);
lean_closure_set(v___x_449_, 0, v___x_448_);
v___x_450_ = lean_unsigned_to_nat(405u);
v___x_451_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
return v___x_451_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_StageCompile(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_PredEval(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_StageCompile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Pancake_PredEval_ctxPut = _init_lp_orb_x2dcompiler_Pancake_PredEval_ctxPut();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_PredEval_ctxPut);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
