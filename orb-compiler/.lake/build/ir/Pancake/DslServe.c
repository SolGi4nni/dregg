// Lean compiler output
// Module: Pancake.DslServe
// Imports: public import Init public meta import Init public import Pancake.ServeSlice
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_sb(lean_object*);
extern lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders;
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
uint8_t l_BitVec_slt(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_BitVec_repr(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_build(lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_serializeWire(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_methodDisallowed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_methodDisallowed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_bodyOver_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_bodyOver_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_always_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_always_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Pancake.DslServe.ReqPred.methodDisallowed"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Pancake.DslServe.ReqPred.always"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__3_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5;
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Pancake.DslServe.ReqPred.bodyOver"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__6_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__7_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__8_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_eval___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_eval___closed__0;
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_eval(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_eval___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__2_value;
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__5_value;
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__8;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__10_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Pancake.DslServe.BodyLoop.appendConst"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr___closed__2_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_BodyLoop_apply(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_BodyLoop_deltaLen(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_BodyLoop_deltaLen___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_BodyLoop_apply_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_BodyLoop_apply_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_instReprBodyLoop_repr_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_instReprBodyLoop_repr_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_addHeader_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_addHeader_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_setStatus_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_setStatus_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_gate_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_gate_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_rewriteBody_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_rewriteBody_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_seq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_seq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_condR_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_condR_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Pancake.DslServe.StageProg.addHeader"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__2_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Pancake.DslServe.StageProg.setStatus"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__3_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__5_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Pancake.DslServe.StageProg.gate"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__6_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__7_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__8_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Pancake.DslServe.StageProg.rewriteBody"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__9_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__10_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__11_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Pancake.DslServe.StageProg.seq"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__12_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__12_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__13_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__14_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Pancake.DslServe.StageProg.condR"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__15 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__15_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__15_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__16 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__16_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__16_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__17 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__17_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "OK"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__3;
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Payload Too Large"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__4_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__5;
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Method Not Allowed"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__6_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__7;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_reasonOf(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_denoteStep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_denote(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_compileStep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_compileWire(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_compileWire___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_compile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_compile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_dToC(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_compileStep_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_compileStep_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_denoteStep_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_denoteStep_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_emptyBase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_emptyBase___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_emptyBase___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_emptyBase = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_emptyBase___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_seqAddHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_seqAddHeaders___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_seqAddHeaders___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_seqAddHeaders(lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hello\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__6;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_okStage;
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Allow"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "GET, POST, HEAD, OPTIONS"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__5;
static const lean_string_object lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "method not allowed\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__6_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__8;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__10;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__11;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_refuseStage;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1000000) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__0_value),((lean_object*)(((size_t)(413) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__3;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_serveProg;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 1)
{
lean_object* v_limit_9_; lean_object* v___x_10_; 
v_limit_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_limit_9_);
lean_dec_ref(v_t_7_);
v___x_10_ = lean_apply_1(v_k_8_, v_limit_9_);
return v___x_10_;
}
else
{
lean_dec(v_t_7_);
return v_k_8_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_methodDisallowed_elim___redArg(lean_object* v_t_23_, lean_object* v_methodDisallowed_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorElim___redArg(v_t_23_, v_methodDisallowed_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_methodDisallowed_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_methodDisallowed_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorElim___redArg(v_t_27_, v_methodDisallowed_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_bodyOver_elim___redArg(lean_object* v_t_31_, lean_object* v_bodyOver_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorElim___redArg(v_t_31_, v_bodyOver_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_bodyOver_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_bodyOver_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorElim___redArg(v_t_35_, v_bodyOver_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_always_elim___redArg(lean_object* v_t_39_, lean_object* v_always_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorElim___redArg(v_t_39_, v_always_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_always_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_always_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_ctorElim___redArg(v_t_43_, v_always_45_);
return v___x_46_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_unsigned_to_nat(2u);
v___x_54_ = lean_nat_to_int(v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_unsigned_to_nat(1u);
v___x_56_ = lean_nat_to_int(v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr(lean_object* v_x_63_, lean_object* v_prec_64_){
_start:
{
lean_object* v___y_66_; lean_object* v___y_73_; 
switch(lean_obj_tag(v_x_63_))
{
case 0:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(1024u);
v___x_80_ = lean_nat_dec_le(v___x_79_, v_prec_64_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4);
v___y_66_ = v___x_81_;
goto v___jp_65_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5);
v___y_66_ = v___x_82_;
goto v___jp_65_;
}
}
case 1:
{
lean_object* v_limit_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_103_; 
v_limit_83_ = lean_ctor_get(v_x_63_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v_x_63_);
if (v_isSharedCheck_103_ == 0)
{
v___x_85_ = v_x_63_;
v_isShared_86_ = v_isSharedCheck_103_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_limit_83_);
lean_dec(v_x_63_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_103_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___y_88_; lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(1024u);
v___x_100_ = lean_nat_dec_le(v___x_99_, v_prec_64_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4);
v___y_88_ = v___x_101_;
goto v___jp_87_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5);
v___y_88_ = v___x_102_;
goto v___jp_87_;
}
v___jp_87_:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_89_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__8));
v___x_90_ = l_Nat_reprFast(v_limit_83_);
if (v_isShared_86_ == 0)
{
lean_ctor_set_tag(v___x_85_, 3);
lean_ctor_set(v___x_85_, 0, v___x_90_);
v___x_92_ = v___x_85_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_90_);
v___x_92_ = v_reuseFailAlloc_98_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_89_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
lean_inc(v___y_88_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___y_88_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = 0;
v___x_96_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_95_);
v___x_97_ = l_Repr_addAppParen(v___x_96_, v_prec_64_);
return v___x_97_;
}
}
}
}
default: 
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(1024u);
v___x_105_ = lean_nat_dec_le(v___x_104_, v_prec_64_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4);
v___y_73_ = v___x_106_;
goto v___jp_72_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5);
v___y_73_ = v___x_107_;
goto v___jp_72_;
}
}
}
v___jp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_67_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__1));
lean_inc(v___y_66_);
v___x_68_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_68_, 0, v___y_66_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = 0;
v___x_70_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_70_, 0, v___x_68_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*1, v___x_69_);
v___x_71_ = l_Repr_addAppParen(v___x_70_, v_prec_64_);
return v___x_71_;
}
v___jp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_74_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__3));
lean_inc(v___y_73_);
v___x_75_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_75_, 0, v___y_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = 0;
v___x_77_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*1, v___x_76_);
v___x_78_ = l_Repr_addAppParen(v___x_77_, v_prec_64_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___boxed(lean_object* v_x_108_, lean_object* v_prec_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr(v_x_108_, v_prec_109_);
lean_dec(v_prec_109_);
return v_res_110_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_eval___closed__0(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_unsigned_to_nat(4u);
v___x_114_ = lean_unsigned_to_nat(64u);
v___x_115_ = l_BitVec_ofNat(v___x_114_, v___x_113_);
return v___x_115_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_eval(lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
switch(lean_obj_tag(v_x_116_))
{
case 0:
{
lean_object* v_method_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_method_118_ = lean_ctor_get(v_x_117_, 0);
lean_inc(v_method_118_);
lean_dec_ref(v_x_117_);
v___x_119_ = lean_unsigned_to_nat(64u);
v___x_120_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_eval___closed__0, &lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_eval___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_eval___closed__0);
v___x_121_ = l_BitVec_slt(v___x_119_, v_method_118_, v___x_120_);
if (v___x_121_ == 0)
{
uint8_t v___x_122_; 
v___x_122_ = 1;
return v___x_122_;
}
else
{
uint8_t v___x_123_; 
v___x_123_ = 0;
return v___x_123_;
}
}
case 1:
{
lean_object* v_limit_124_; lean_object* v_bodyLen_125_; uint8_t v___x_126_; 
v_limit_124_ = lean_ctor_get(v_x_116_, 0);
v_bodyLen_125_ = lean_ctor_get(v_x_117_, 1);
lean_inc(v_bodyLen_125_);
lean_dec_ref(v_x_117_);
v___x_126_ = lean_nat_dec_lt(v_limit_124_, v_bodyLen_125_);
lean_dec(v_bodyLen_125_);
return v___x_126_;
}
default: 
{
uint8_t v___x_127_; 
lean_dec_ref(v_x_117_);
v___x_127_ = 1;
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_eval___boxed(lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_eval(v_x_128_, v_x_129_);
lean_dec(v_x_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0_spec__0_spec__1(lean_object* v_x_132_, lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
lean_dec(v_x_132_);
return v_x_133_;
}
else
{
lean_object* v_head_135_; lean_object* v_tail_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_147_; 
v_head_135_ = lean_ctor_get(v_x_134_, 0);
v_tail_136_ = lean_ctor_get(v_x_134_, 1);
v_isSharedCheck_147_ = !lean_is_exclusive(v_x_134_);
if (v_isSharedCheck_147_ == 0)
{
v___x_138_ = v_x_134_;
v_isShared_139_ = v_isSharedCheck_147_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_tail_136_);
lean_inc(v_head_135_);
lean_dec(v_x_134_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_147_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_140_ = lean_unsigned_to_nat(8u);
lean_inc(v_x_132_);
if (v_isShared_139_ == 0)
{
lean_ctor_set_tag(v___x_138_, 5);
lean_ctor_set(v___x_138_, 1, v_x_132_);
lean_ctor_set(v___x_138_, 0, v_x_133_);
v___x_142_ = v___x_138_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_x_133_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_x_132_);
v___x_142_ = v_reuseFailAlloc_146_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = l_BitVec_repr(v___x_140_, v_head_135_);
v___x_144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_142_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v_x_133_ = v___x_144_;
v_x_134_ = v_tail_136_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0_spec__0(lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
lean_object* v___x_150_; 
lean_dec(v_x_149_);
v___x_150_ = lean_box(0);
return v___x_150_;
}
else
{
lean_object* v_head_151_; lean_object* v_tail_152_; lean_object* v___x_153_; 
v_head_151_ = lean_ctor_get(v_x_148_, 0);
lean_inc(v_head_151_);
v_tail_152_ = lean_ctor_get(v_x_148_, 1);
lean_inc(v_tail_152_);
lean_dec_ref(v_x_148_);
v___x_153_ = lean_unsigned_to_nat(8u);
if (lean_obj_tag(v_tail_152_) == 0)
{
lean_object* v___x_154_; 
lean_dec(v_x_149_);
v___x_154_ = l_BitVec_repr(v___x_153_, v_head_151_);
return v___x_154_;
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = l_BitVec_repr(v___x_153_, v_head_151_);
v___x_156_ = lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0_spec__0_spec__1(v_x_149_, v___x_155_, v_tail_152_);
return v___x_156_;
}
}
}
}
static lean_object* _init_lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__2));
v___x_169_ = lean_string_length(v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_obj_once(&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__7, &lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__7_once, _init_lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__7);
v___x_171_ = lean_nat_to_int(v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg(lean_object* v_a_176_){
_start:
{
if (lean_obj_tag(v_a_176_) == 0)
{
lean_object* v___x_177_; 
v___x_177_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__1));
return v___x_177_;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; lean_object* v___x_187_; 
v___x_178_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__5));
v___x_179_ = lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0_spec__0(v_a_176_, v___x_178_);
v___x_180_ = lean_obj_once(&lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__8, &lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__8_once, _init_lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__8);
v___x_181_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__9));
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_179_);
v___x_183_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg___closed__10));
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_180_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = 0;
v___x_187_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_187_, 0, v___x_185_);
lean_ctor_set_uint8(v___x_187_, sizeof(void*)*1, v___x_186_);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr(lean_object* v_x_194_, lean_object* v_prec_195_){
_start:
{
lean_object* v___y_197_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(1024u);
v___x_206_ = lean_nat_dec_le(v___x_205_, v_prec_195_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; 
v___x_207_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4);
v___y_197_ = v___x_207_;
goto v___jp_196_;
}
else
{
lean_object* v___x_208_; 
v___x_208_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5);
v___y_197_ = v___x_208_;
goto v___jp_196_;
}
v___jp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_198_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr___closed__2));
v___x_199_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg(v_x_194_);
v___x_200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
lean_inc(v___y_197_);
v___x_201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_201_, 0, v___y_197_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = 0;
v___x_203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*1, v___x_202_);
v___x_204_ = l_Repr_addAppParen(v___x_203_, v_prec_195_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr___boxed(lean_object* v_x_209_, lean_object* v_prec_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr(v_x_209_, v_prec_210_);
lean_dec(v_prec_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0(lean_object* v_a_212_, lean_object* v_n_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg(v_a_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___boxed(lean_object* v_a_215_, lean_object* v_n_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0(v_a_215_, v_n_216_);
lean_dec(v_n_216_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_BodyLoop_apply(lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_List_appendTR___redArg(v_x_221_, v_x_220_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_BodyLoop_deltaLen(lean_object* v_x_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_List_lengthTR___redArg(v_x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_BodyLoop_deltaLen___boxed(lean_object* v_x_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = lp_orb_x2dcompiler_Pancake_DslServe_BodyLoop_deltaLen(v_x_225_);
lean_dec(v_x_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_BodyLoop_apply_match__1_splitter___redArg(lean_object* v_x_227_, lean_object* v_x_228_, lean_object* v_h__1_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = lean_apply_2(v_h__1_229_, v_x_227_, v_x_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_BodyLoop_apply_match__1_splitter(lean_object* v_motive_231_, lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v_h__1_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lean_apply_2(v_h__1_234_, v_x_232_, v_x_233_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_instReprBodyLoop_repr_match__1_splitter___redArg(lean_object* v_x_236_, lean_object* v_h__1_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_apply_1(v_h__1_237_, v_x_236_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_instReprBodyLoop_repr_match__1_splitter(lean_object* v_motive_239_, lean_object* v_x_240_, lean_object* v_h__1_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = lean_apply_1(v_h__1_241_, v_x_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorIdx(lean_object* v_x_243_){
_start:
{
switch(lean_obj_tag(v_x_243_))
{
case 0:
{
lean_object* v___x_244_; 
v___x_244_ = lean_unsigned_to_nat(0u);
return v___x_244_;
}
case 1:
{
lean_object* v___x_245_; 
v___x_245_ = lean_unsigned_to_nat(1u);
return v___x_245_;
}
case 2:
{
lean_object* v___x_246_; 
v___x_246_ = lean_unsigned_to_nat(2u);
return v___x_246_;
}
case 3:
{
lean_object* v___x_247_; 
v___x_247_ = lean_unsigned_to_nat(3u);
return v___x_247_;
}
case 4:
{
lean_object* v___x_248_; 
v___x_248_ = lean_unsigned_to_nat(4u);
return v___x_248_;
}
default: 
{
lean_object* v___x_249_; 
v___x_249_ = lean_unsigned_to_nat(5u);
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorIdx___boxed(lean_object* v_x_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorIdx(v_x_250_);
lean_dec_ref(v_x_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___redArg(lean_object* v_t_252_, lean_object* v_k_253_){
_start:
{
switch(lean_obj_tag(v_t_252_))
{
case 3:
{
lean_object* v_t_254_; lean_object* v___x_255_; 
v_t_254_ = lean_ctor_get(v_t_252_, 0);
lean_inc(v_t_254_);
lean_dec_ref(v_t_252_);
v___x_255_ = lean_apply_1(v_k_253_, v_t_254_);
return v___x_255_;
}
case 4:
{
lean_object* v_a_256_; lean_object* v_b_257_; lean_object* v___x_258_; 
v_a_256_ = lean_ctor_get(v_t_252_, 0);
lean_inc_ref(v_a_256_);
v_b_257_ = lean_ctor_get(v_t_252_, 1);
lean_inc_ref(v_b_257_);
lean_dec_ref(v_t_252_);
v___x_258_ = lean_apply_2(v_k_253_, v_a_256_, v_b_257_);
return v___x_258_;
}
case 5:
{
lean_object* v_c_259_; lean_object* v_a_260_; lean_object* v_b_261_; lean_object* v___x_262_; 
v_c_259_ = lean_ctor_get(v_t_252_, 0);
lean_inc(v_c_259_);
v_a_260_ = lean_ctor_get(v_t_252_, 1);
lean_inc_ref(v_a_260_);
v_b_261_ = lean_ctor_get(v_t_252_, 2);
lean_inc_ref(v_b_261_);
lean_dec_ref(v_t_252_);
v___x_262_ = lean_apply_3(v_k_253_, v_c_259_, v_a_260_, v_b_261_);
return v___x_262_;
}
default: 
{
lean_object* v_name_263_; lean_object* v_val_264_; lean_object* v___x_265_; 
v_name_263_ = lean_ctor_get(v_t_252_, 0);
lean_inc(v_name_263_);
v_val_264_ = lean_ctor_get(v_t_252_, 1);
lean_inc(v_val_264_);
lean_dec_ref(v_t_252_);
v___x_265_ = lean_apply_2(v_k_253_, v_name_263_, v_val_264_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim(lean_object* v_motive_266_, lean_object* v_ctorIdx_267_, lean_object* v_t_268_, lean_object* v_h_269_, lean_object* v_k_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___redArg(v_t_268_, v_k_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___boxed(lean_object* v_motive_272_, lean_object* v_ctorIdx_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_k_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim(v_motive_272_, v_ctorIdx_273_, v_t_274_, v_h_275_, v_k_276_);
lean_dec(v_ctorIdx_273_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_addHeader_elim___redArg(lean_object* v_t_278_, lean_object* v_addHeader_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___redArg(v_t_278_, v_addHeader_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_addHeader_elim(lean_object* v_motive_281_, lean_object* v_t_282_, lean_object* v_h_283_, lean_object* v_addHeader_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___redArg(v_t_282_, v_addHeader_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_setStatus_elim___redArg(lean_object* v_t_286_, lean_object* v_setStatus_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___redArg(v_t_286_, v_setStatus_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_setStatus_elim(lean_object* v_motive_289_, lean_object* v_t_290_, lean_object* v_h_291_, lean_object* v_setStatus_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___redArg(v_t_290_, v_setStatus_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_gate_elim___redArg(lean_object* v_t_294_, lean_object* v_gate_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___redArg(v_t_294_, v_gate_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_gate_elim(lean_object* v_motive_297_, lean_object* v_t_298_, lean_object* v_h_299_, lean_object* v_gate_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___redArg(v_t_298_, v_gate_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_rewriteBody_elim___redArg(lean_object* v_t_302_, lean_object* v_rewriteBody_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___redArg(v_t_302_, v_rewriteBody_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_rewriteBody_elim(lean_object* v_motive_305_, lean_object* v_t_306_, lean_object* v_h_307_, lean_object* v_rewriteBody_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___redArg(v_t_306_, v_rewriteBody_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_seq_elim___redArg(lean_object* v_t_310_, lean_object* v_seq_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___redArg(v_t_310_, v_seq_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_seq_elim(lean_object* v_motive_313_, lean_object* v_t_314_, lean_object* v_h_315_, lean_object* v_seq_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___redArg(v_t_314_, v_seq_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_condR_elim___redArg(lean_object* v_t_318_, lean_object* v_condR_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___redArg(v_t_318_, v_condR_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_StageProg_condR_elim(lean_object* v_motive_321_, lean_object* v_t_322_, lean_object* v_h_323_, lean_object* v_condR_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lp_orb_x2dcompiler_Pancake_DslServe_StageProg_ctorElim___redArg(v_t_322_, v_condR_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr(lean_object* v_x_362_, lean_object* v_prec_363_){
_start:
{
switch(lean_obj_tag(v_x_362_))
{
case 0:
{
lean_object* v_name_364_; lean_object* v_val_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_388_; 
v_name_364_ = lean_ctor_get(v_x_362_, 0);
v_val_365_ = lean_ctor_get(v_x_362_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v_x_362_);
if (v_isSharedCheck_388_ == 0)
{
v___x_367_ = v_x_362_;
v_isShared_368_ = v_isSharedCheck_388_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_val_365_);
lean_inc(v_name_364_);
lean_dec(v_x_362_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_388_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___y_370_; lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = lean_unsigned_to_nat(1024u);
v___x_385_ = lean_nat_dec_le(v___x_384_, v_prec_363_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
v___x_386_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4);
v___y_370_ = v___x_386_;
goto v___jp_369_;
}
else
{
lean_object* v___x_387_; 
v___x_387_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5);
v___y_370_ = v___x_387_;
goto v___jp_369_;
}
v___jp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_371_ = lean_box(1);
v___x_372_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__2));
v___x_373_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg(v_name_364_);
if (v_isShared_368_ == 0)
{
lean_ctor_set_tag(v___x_367_, 5);
lean_ctor_set(v___x_367_, 1, v___x_373_);
lean_ctor_set(v___x_367_, 0, v___x_372_);
v___x_375_ = v___x_367_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_383_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_371_);
v___x_377_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg(v_val_365_);
v___x_378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
lean_inc(v___y_370_);
v___x_379_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_379_, 0, v___y_370_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = 0;
v___x_381_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*1, v___x_380_);
v___x_382_ = l_Repr_addAppParen(v___x_381_, v_prec_363_);
return v___x_382_;
}
}
}
}
case 1:
{
lean_object* v_code_389_; lean_object* v_reason_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_414_; 
v_code_389_ = lean_ctor_get(v_x_362_, 0);
v_reason_390_ = lean_ctor_get(v_x_362_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_x_362_);
if (v_isSharedCheck_414_ == 0)
{
v___x_392_ = v_x_362_;
v_isShared_393_ = v_isSharedCheck_414_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_reason_390_);
lean_inc(v_code_389_);
lean_dec(v_x_362_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_414_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___y_395_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_unsigned_to_nat(1024u);
v___x_411_ = lean_nat_dec_le(v___x_410_, v_prec_363_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
v___x_412_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4);
v___y_395_ = v___x_412_;
goto v___jp_394_;
}
else
{
lean_object* v___x_413_; 
v___x_413_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5);
v___y_395_ = v___x_413_;
goto v___jp_394_;
}
v___jp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_396_ = lean_box(1);
v___x_397_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__5));
v___x_398_ = l_Nat_reprFast(v_code_389_);
v___x_399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
if (v_isShared_393_ == 0)
{
lean_ctor_set_tag(v___x_392_, 5);
lean_ctor_set(v___x_392_, 1, v___x_399_);
lean_ctor_set(v___x_392_, 0, v___x_397_);
v___x_401_ = v___x_392_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v___x_399_);
v___x_401_ = v_reuseFailAlloc_409_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_402_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_396_);
v___x_403_ = lp_orb_x2dcompiler_List_repr___at___00Pancake_DslServe_instReprBodyLoop_repr_spec__0___redArg(v_reason_390_);
v___x_404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_402_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
lean_inc(v___y_395_);
v___x_405_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_405_, 0, v___y_395_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = 0;
v___x_407_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*1, v___x_406_);
v___x_408_ = l_Repr_addAppParen(v___x_407_, v_prec_363_);
return v___x_408_;
}
}
}
}
case 2:
{
lean_object* v_c_415_; lean_object* v_code_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_441_; 
v_c_415_ = lean_ctor_get(v_x_362_, 0);
v_code_416_ = lean_ctor_get(v_x_362_, 1);
v_isSharedCheck_441_ = !lean_is_exclusive(v_x_362_);
if (v_isSharedCheck_441_ == 0)
{
v___x_418_ = v_x_362_;
v_isShared_419_ = v_isSharedCheck_441_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_code_416_);
lean_inc(v_c_415_);
lean_dec(v_x_362_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_441_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___y_421_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_unsigned_to_nat(1024u);
v___x_438_ = lean_nat_dec_le(v___x_437_, v_prec_363_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
v___x_439_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4);
v___y_421_ = v___x_439_;
goto v___jp_420_;
}
else
{
lean_object* v___x_440_; 
v___x_440_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5);
v___y_421_ = v___x_440_;
goto v___jp_420_;
}
v___jp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_422_ = lean_box(1);
v___x_423_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__8));
v___x_424_ = lean_unsigned_to_nat(1024u);
v___x_425_ = lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr(v_c_415_, v___x_424_);
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 5);
lean_ctor_set(v___x_418_, 1, v___x_425_);
lean_ctor_set(v___x_418_, 0, v___x_423_);
v___x_427_ = v___x_418_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v___x_425_);
v___x_427_ = v_reuseFailAlloc_436_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_428_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___x_422_);
v___x_429_ = l_Nat_reprFast(v_code_416_);
v___x_430_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
v___x_431_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_428_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
lean_inc(v___y_421_);
v___x_432_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_432_, 0, v___y_421_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = 0;
v___x_434_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*1, v___x_433_);
v___x_435_ = l_Repr_addAppParen(v___x_434_, v_prec_363_);
return v___x_435_;
}
}
}
}
case 3:
{
lean_object* v_t_442_; lean_object* v___y_444_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_t_442_ = lean_ctor_get(v_x_362_, 0);
lean_inc(v_t_442_);
lean_dec_ref(v_x_362_);
v___x_453_ = lean_unsigned_to_nat(1024u);
v___x_454_ = lean_nat_dec_le(v___x_453_, v_prec_363_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
v___x_455_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4);
v___y_444_ = v___x_455_;
goto v___jp_443_;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5);
v___y_444_ = v___x_456_;
goto v___jp_443_;
}
v___jp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_445_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__11));
v___x_446_ = lean_unsigned_to_nat(1024u);
v___x_447_ = lp_orb_x2dcompiler_Pancake_DslServe_instReprBodyLoop_repr(v_t_442_, v___x_446_);
v___x_448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_445_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
lean_inc(v___y_444_);
v___x_449_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_449_, 0, v___y_444_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = 0;
v___x_451_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*1, v___x_450_);
v___x_452_ = l_Repr_addAppParen(v___x_451_, v_prec_363_);
return v___x_452_;
}
}
case 4:
{
lean_object* v_a_457_; lean_object* v_b_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_481_; 
v_a_457_ = lean_ctor_get(v_x_362_, 0);
v_b_458_ = lean_ctor_get(v_x_362_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_x_362_);
if (v_isSharedCheck_481_ == 0)
{
v___x_460_ = v_x_362_;
v_isShared_461_ = v_isSharedCheck_481_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_b_458_);
lean_inc(v_a_457_);
lean_dec(v_x_362_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_481_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___y_464_; uint8_t v___x_478_; 
v___x_462_ = lean_unsigned_to_nat(1024u);
v___x_478_ = lean_nat_dec_le(v___x_462_, v_prec_363_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
v___x_479_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4);
v___y_464_ = v___x_479_;
goto v___jp_463_;
}
else
{
lean_object* v___x_480_; 
v___x_480_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5);
v___y_464_ = v___x_480_;
goto v___jp_463_;
}
v___jp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_465_ = lean_box(1);
v___x_466_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__14));
v___x_467_ = lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr(v_a_457_, v___x_462_);
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 5);
lean_ctor_set(v___x_460_, 1, v___x_467_);
lean_ctor_set(v___x_460_, 0, v___x_466_);
v___x_469_ = v___x_460_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_467_);
v___x_469_ = v_reuseFailAlloc_477_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_465_);
v___x_471_ = lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr(v_b_458_, v___x_462_);
v___x_472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
lean_inc(v___y_464_);
v___x_473_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_473_, 0, v___y_464_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = 0;
v___x_475_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_475_, 0, v___x_473_);
lean_ctor_set_uint8(v___x_475_, sizeof(void*)*1, v___x_474_);
v___x_476_ = l_Repr_addAppParen(v___x_475_, v_prec_363_);
return v___x_476_;
}
}
}
}
default: 
{
lean_object* v_c_482_; lean_object* v_a_483_; lean_object* v_b_484_; lean_object* v___x_485_; lean_object* v___y_487_; uint8_t v___x_502_; 
v_c_482_ = lean_ctor_get(v_x_362_, 0);
lean_inc(v_c_482_);
v_a_483_ = lean_ctor_get(v_x_362_, 1);
lean_inc_ref(v_a_483_);
v_b_484_ = lean_ctor_get(v_x_362_, 2);
lean_inc_ref(v_b_484_);
lean_dec_ref(v_x_362_);
v___x_485_ = lean_unsigned_to_nat(1024u);
v___x_502_ = lean_nat_dec_le(v___x_485_, v_prec_363_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
v___x_503_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__4);
v___y_487_ = v___x_503_;
goto v___jp_486_;
}
else
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5, &lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr___closed__5);
v___y_487_ = v___x_504_;
goto v___jp_486_;
}
v___jp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_488_ = lean_box(1);
v___x_489_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___closed__17));
v___x_490_ = lp_orb_x2dcompiler_Pancake_DslServe_instReprReqPred_repr(v_c_482_, v___x_485_);
v___x_491_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___x_488_);
v___x_493_ = lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr(v_a_483_, v___x_485_);
v___x_494_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_488_);
v___x_496_ = lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr(v_b_484_, v___x_485_);
v___x_497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_495_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
lean_inc(v___y_487_);
v___x_498_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_498_, 0, v___y_487_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = 0;
v___x_500_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*1, v___x_499_);
v___x_501_ = l_Repr_addAppParen(v___x_500_, v_prec_363_);
return v___x_501_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr___boxed(lean_object* v_x_505_, lean_object* v_prec_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = lp_orb_x2dcompiler_Pancake_DslServe_instReprStageProg_repr(v_x_505_, v_prec_506_);
lean_dec(v_prec_506_);
return v_res_507_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__1(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__0));
v___x_512_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__3(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__2));
v___x_515_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__5(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__4));
v___x_518_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_517_);
return v___x_518_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__7(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__6));
v___x_521_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_reasonOf(lean_object* v_code_522_){
_start:
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_unsigned_to_nat(405u);
v___x_524_ = lean_nat_dec_eq(v_code_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(413u);
v___x_526_ = lean_nat_dec_eq(v_code_522_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_unsigned_to_nat(200u);
v___x_528_ = lean_nat_dec_eq(v_code_522_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
v___x_529_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__1, &lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__1);
return v___x_529_;
}
else
{
lean_object* v___x_530_; 
v___x_530_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__3, &lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__3);
return v___x_530_;
}
}
else
{
lean_object* v___x_531_; 
v___x_531_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__5, &lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__5);
return v___x_531_;
}
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__7, &lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__7);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___boxed(lean_object* v_code_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = lp_orb_x2dcompiler_Pancake_DslServe_reasonOf(v_code_533_);
lean_dec(v_code_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_denoteStep(lean_object* v_c_535_, lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
switch(lean_obj_tag(v_x_537_))
{
case 0:
{
lean_object* v_resp_538_; lean_object* v_name_539_; lean_object* v_val_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_570_; 
lean_dec_ref(v_c_535_);
v_resp_538_ = lean_ctor_get(v_x_536_, 0);
lean_inc_ref(v_resp_538_);
v_name_539_ = lean_ctor_get(v_x_537_, 0);
v_val_540_ = lean_ctor_get(v_x_537_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_x_537_);
if (v_isSharedCheck_570_ == 0)
{
v___x_542_ = v_x_537_;
v_isShared_543_ = v_isSharedCheck_570_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_val_540_);
lean_inc(v_name_539_);
lean_dec(v_x_537_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_570_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
uint8_t v_gated_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_568_; 
v_gated_544_ = lean_ctor_get_uint8(v_x_536_, sizeof(void*)*1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; 
v_unused_569_ = lean_ctor_get(v_x_536_, 0);
lean_dec(v_unused_569_);
v___x_546_ = v_x_536_;
v_isShared_547_ = v_isSharedCheck_568_;
goto v_resetjp_545_;
}
else
{
lean_dec(v_x_536_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_568_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v_status_548_; lean_object* v_reason_549_; lean_object* v_headers_550_; lean_object* v_body_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_567_; 
v_status_548_ = lean_ctor_get(v_resp_538_, 0);
v_reason_549_ = lean_ctor_get(v_resp_538_, 1);
v_headers_550_ = lean_ctor_get(v_resp_538_, 2);
v_body_551_ = lean_ctor_get(v_resp_538_, 3);
v_isSharedCheck_567_ = !lean_is_exclusive(v_resp_538_);
if (v_isSharedCheck_567_ == 0)
{
v___x_553_ = v_resp_538_;
v_isShared_554_ = v_isSharedCheck_567_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_body_551_);
lean_inc(v_headers_550_);
lean_inc(v_reason_549_);
lean_inc(v_status_548_);
lean_dec(v_resp_538_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_567_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_543_ == 0)
{
v___x_556_ = v___x_542_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_name_539_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_val_540_);
v___x_556_ = v_reuseFailAlloc_566_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_557_ = lean_box(0);
v___x_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = l_List_appendTR___redArg(v_headers_550_, v___x_558_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 2, v___x_559_);
v___x_561_ = v___x_553_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_status_548_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_reason_549_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v_body_551_);
v___x_561_ = v_reuseFailAlloc_565_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_563_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_561_);
v___x_563_ = v___x_546_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
lean_ctor_set_uint8(v_reuseFailAlloc_564_, sizeof(void*)*1, v_gated_544_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
}
}
case 1:
{
uint8_t v_gated_571_; 
lean_dec_ref(v_c_535_);
v_gated_571_ = lean_ctor_get_uint8(v_x_536_, sizeof(void*)*1);
if (v_gated_571_ == 0)
{
lean_object* v_resp_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_592_; 
v_resp_572_ = lean_ctor_get(v_x_536_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_592_ == 0)
{
v___x_574_ = v_x_536_;
v_isShared_575_ = v_isSharedCheck_592_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_resp_572_);
lean_dec(v_x_536_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_592_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v_code_576_; lean_object* v_reason_577_; lean_object* v_headers_578_; lean_object* v_body_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_589_; 
v_code_576_ = lean_ctor_get(v_x_537_, 0);
lean_inc(v_code_576_);
v_reason_577_ = lean_ctor_get(v_x_537_, 1);
lean_inc(v_reason_577_);
lean_dec_ref(v_x_537_);
v_headers_578_ = lean_ctor_get(v_resp_572_, 2);
v_body_579_ = lean_ctor_get(v_resp_572_, 3);
v_isSharedCheck_589_ = !lean_is_exclusive(v_resp_572_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; lean_object* v_unused_591_; 
v_unused_590_ = lean_ctor_get(v_resp_572_, 1);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_resp_572_, 0);
lean_dec(v_unused_591_);
v___x_581_ = v_resp_572_;
v_isShared_582_ = v_isSharedCheck_589_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_body_579_);
lean_inc(v_headers_578_);
lean_dec(v_resp_572_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_589_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v_reason_577_);
lean_ctor_set(v___x_581_, 0, v_code_576_);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_code_576_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_reason_577_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_headers_578_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v_body_579_);
v___x_584_ = v_reuseFailAlloc_588_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_586_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_584_);
v___x_586_ = v___x_574_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
lean_ctor_set_uint8(v_reuseFailAlloc_587_, sizeof(void*)*1, v_gated_571_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_537_);
return v_x_536_;
}
}
case 2:
{
uint8_t v_gated_593_; 
v_gated_593_ = lean_ctor_get_uint8(v_x_536_, sizeof(void*)*1);
if (v_gated_593_ == 0)
{
lean_object* v_c_594_; lean_object* v_code_595_; lean_object* v_resp_596_; uint8_t v___x_597_; 
v_c_594_ = lean_ctor_get(v_x_537_, 0);
lean_inc(v_c_594_);
v_code_595_ = lean_ctor_get(v_x_537_, 1);
lean_inc(v_code_595_);
lean_dec_ref(v_x_537_);
v_resp_596_ = lean_ctor_get(v_x_536_, 0);
lean_inc_ref(v_resp_596_);
v___x_597_ = lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_eval(v_c_594_, v_c_535_);
lean_dec(v_c_594_);
if (v___x_597_ == 0)
{
lean_dec_ref(v_resp_596_);
lean_dec(v_code_595_);
return v_x_536_;
}
else
{
lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_616_; 
v_isSharedCheck_616_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v_x_536_, 0);
lean_dec(v_unused_617_);
v___x_599_ = v_x_536_;
v_isShared_600_ = v_isSharedCheck_616_;
goto v_resetjp_598_;
}
else
{
lean_dec(v_x_536_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_616_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v_headers_601_; lean_object* v_body_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_613_; 
v_headers_601_ = lean_ctor_get(v_resp_596_, 2);
v_body_602_ = lean_ctor_get(v_resp_596_, 3);
v_isSharedCheck_613_ = !lean_is_exclusive(v_resp_596_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; lean_object* v_unused_615_; 
v_unused_614_ = lean_ctor_get(v_resp_596_, 1);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_resp_596_, 0);
lean_dec(v_unused_615_);
v___x_604_ = v_resp_596_;
v_isShared_605_ = v_isSharedCheck_613_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_body_602_);
lean_inc(v_headers_601_);
lean_dec(v_resp_596_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_613_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = lp_orb_x2dcompiler_Pancake_DslServe_reasonOf(v_code_595_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v___x_606_);
lean_ctor_set(v___x_604_, 0, v_code_595_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_code_595_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_headers_601_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_body_602_);
v___x_608_ = v_reuseFailAlloc_612_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_610_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_608_);
v___x_610_ = v___x_599_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*1, v___x_597_);
return v___x_610_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_x_537_);
lean_dec_ref(v_c_535_);
return v_x_536_;
}
}
case 3:
{
lean_object* v_resp_618_; lean_object* v_t_619_; uint8_t v_gated_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_639_; 
lean_dec_ref(v_c_535_);
v_resp_618_ = lean_ctor_get(v_x_536_, 0);
lean_inc_ref(v_resp_618_);
v_t_619_ = lean_ctor_get(v_x_537_, 0);
lean_inc(v_t_619_);
lean_dec_ref(v_x_537_);
v_gated_620_ = lean_ctor_get_uint8(v_x_536_, sizeof(void*)*1);
v_isSharedCheck_639_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; 
v_unused_640_ = lean_ctor_get(v_x_536_, 0);
lean_dec(v_unused_640_);
v___x_622_ = v_x_536_;
v_isShared_623_ = v_isSharedCheck_639_;
goto v_resetjp_621_;
}
else
{
lean_dec(v_x_536_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_639_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_status_624_; lean_object* v_reason_625_; lean_object* v_headers_626_; lean_object* v_body_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_638_; 
v_status_624_ = lean_ctor_get(v_resp_618_, 0);
v_reason_625_ = lean_ctor_get(v_resp_618_, 1);
v_headers_626_ = lean_ctor_get(v_resp_618_, 2);
v_body_627_ = lean_ctor_get(v_resp_618_, 3);
v_isSharedCheck_638_ = !lean_is_exclusive(v_resp_618_);
if (v_isSharedCheck_638_ == 0)
{
v___x_629_ = v_resp_618_;
v_isShared_630_ = v_isSharedCheck_638_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_body_627_);
lean_inc(v_headers_626_);
lean_inc(v_reason_625_);
lean_inc(v_status_624_);
lean_dec(v_resp_618_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_638_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = l_List_appendTR___redArg(v_body_627_, v_t_619_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 3, v___x_631_);
v___x_633_ = v___x_629_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_status_624_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_reason_625_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_headers_626_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v___x_631_);
v___x_633_ = v_reuseFailAlloc_637_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_633_);
v___x_635_ = v___x_622_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
lean_ctor_set_uint8(v_reuseFailAlloc_636_, sizeof(void*)*1, v_gated_620_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
case 4:
{
lean_object* v_a_641_; lean_object* v_b_642_; lean_object* v___x_643_; 
v_a_641_ = lean_ctor_get(v_x_537_, 0);
lean_inc_ref(v_a_641_);
v_b_642_ = lean_ctor_get(v_x_537_, 1);
lean_inc_ref(v_b_642_);
lean_dec_ref(v_x_537_);
lean_inc_ref(v_c_535_);
v___x_643_ = lp_orb_x2dcompiler_Pancake_DslServe_denoteStep(v_c_535_, v_x_536_, v_a_641_);
v_x_536_ = v___x_643_;
v_x_537_ = v_b_642_;
goto _start;
}
default: 
{
lean_object* v_c_645_; lean_object* v_a_646_; lean_object* v_b_647_; uint8_t v___x_648_; 
v_c_645_ = lean_ctor_get(v_x_537_, 0);
lean_inc(v_c_645_);
v_a_646_ = lean_ctor_get(v_x_537_, 1);
lean_inc_ref(v_a_646_);
v_b_647_ = lean_ctor_get(v_x_537_, 2);
lean_inc_ref(v_b_647_);
lean_dec_ref(v_x_537_);
lean_inc_ref(v_c_535_);
v___x_648_ = lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_eval(v_c_645_, v_c_535_);
lean_dec(v_c_645_);
if (v___x_648_ == 0)
{
lean_dec_ref(v_a_646_);
v_x_537_ = v_b_647_;
goto _start;
}
else
{
lean_dec_ref(v_b_647_);
v_x_537_ = v_a_646_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_denote(lean_object* v_p_651_, lean_object* v_base_652_, lean_object* v_c_653_){
_start:
{
uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_resp_657_; 
v___x_654_ = 0;
v___x_655_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_655_, 0, v_base_652_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*1, v___x_654_);
v___x_656_ = lp_orb_x2dcompiler_Pancake_DslServe_denoteStep(v_c_653_, v___x_655_, v_p_651_);
v_resp_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc_ref(v_resp_657_);
lean_dec_ref(v___x_656_);
return v_resp_657_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_compileStep(lean_object* v_c_658_, lean_object* v_x_659_, lean_object* v_x_660_){
_start:
{
switch(lean_obj_tag(v_x_660_))
{
case 0:
{
lean_object* v_wire_661_; lean_object* v_name_662_; lean_object* v_val_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_694_; 
lean_dec_ref(v_c_658_);
v_wire_661_ = lean_ctor_get(v_x_659_, 0);
lean_inc_ref(v_wire_661_);
v_name_662_ = lean_ctor_get(v_x_660_, 0);
v_val_663_ = lean_ctor_get(v_x_660_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_x_660_);
if (v_isSharedCheck_694_ == 0)
{
v___x_665_ = v_x_660_;
v_isShared_666_ = v_isSharedCheck_694_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_val_663_);
lean_inc(v_name_662_);
lean_dec(v_x_660_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_694_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
uint8_t v_gated_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_692_; 
v_gated_667_ = lean_ctor_get_uint8(v_x_659_, sizeof(void*)*1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; 
v_unused_693_ = lean_ctor_get(v_x_659_, 0);
lean_dec(v_unused_693_);
v___x_669_ = v_x_659_;
v_isShared_670_ = v_isSharedCheck_692_;
goto v_resetjp_668_;
}
else
{
lean_dec(v_x_659_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_692_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_status_671_; lean_object* v_reason_672_; lean_object* v_headers_673_; lean_object* v_contentLength_674_; lean_object* v_body_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_691_; 
v_status_671_ = lean_ctor_get(v_wire_661_, 0);
v_reason_672_ = lean_ctor_get(v_wire_661_, 1);
v_headers_673_ = lean_ctor_get(v_wire_661_, 2);
v_contentLength_674_ = lean_ctor_get(v_wire_661_, 3);
v_body_675_ = lean_ctor_get(v_wire_661_, 4);
v_isSharedCheck_691_ = !lean_is_exclusive(v_wire_661_);
if (v_isSharedCheck_691_ == 0)
{
v___x_677_ = v_wire_661_;
v_isShared_678_ = v_isSharedCheck_691_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_body_675_);
lean_inc(v_contentLength_674_);
lean_inc(v_headers_673_);
lean_inc(v_reason_672_);
lean_inc(v_status_671_);
lean_dec(v_wire_661_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_691_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_666_ == 0)
{
v___x_680_ = v___x_665_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_name_662_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_val_663_);
v___x_680_ = v_reuseFailAlloc_690_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_681_ = lean_box(0);
v___x_682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = l_List_appendTR___redArg(v_headers_673_, v___x_682_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 2, v___x_683_);
v___x_685_ = v___x_677_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_status_671_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_reason_672_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_689_, 3, v_contentLength_674_);
lean_ctor_set(v_reuseFailAlloc_689_, 4, v_body_675_);
v___x_685_ = v_reuseFailAlloc_689_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_687_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_685_);
v___x_687_ = v___x_669_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
lean_ctor_set_uint8(v_reuseFailAlloc_688_, sizeof(void*)*1, v_gated_667_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
}
}
case 1:
{
uint8_t v_gated_695_; 
lean_dec_ref(v_c_658_);
v_gated_695_ = lean_ctor_get_uint8(v_x_659_, sizeof(void*)*1);
if (v_gated_695_ == 0)
{
lean_object* v_wire_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_717_; 
v_wire_696_ = lean_ctor_get(v_x_659_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_717_ == 0)
{
v___x_698_ = v_x_659_;
v_isShared_699_ = v_isSharedCheck_717_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_wire_696_);
lean_dec(v_x_659_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_717_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_code_700_; lean_object* v_reason_701_; lean_object* v_headers_702_; lean_object* v_contentLength_703_; lean_object* v_body_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_714_; 
v_code_700_ = lean_ctor_get(v_x_660_, 0);
lean_inc(v_code_700_);
v_reason_701_ = lean_ctor_get(v_x_660_, 1);
lean_inc(v_reason_701_);
lean_dec_ref(v_x_660_);
v_headers_702_ = lean_ctor_get(v_wire_696_, 2);
v_contentLength_703_ = lean_ctor_get(v_wire_696_, 3);
v_body_704_ = lean_ctor_get(v_wire_696_, 4);
v_isSharedCheck_714_ = !lean_is_exclusive(v_wire_696_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; lean_object* v_unused_716_; 
v_unused_715_ = lean_ctor_get(v_wire_696_, 1);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_wire_696_, 0);
lean_dec(v_unused_716_);
v___x_706_ = v_wire_696_;
v_isShared_707_ = v_isSharedCheck_714_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_body_704_);
lean_inc(v_contentLength_703_);
lean_inc(v_headers_702_);
lean_dec(v_wire_696_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_714_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v_reason_701_);
lean_ctor_set(v___x_706_, 0, v_code_700_);
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_code_700_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_reason_701_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_headers_702_);
lean_ctor_set(v_reuseFailAlloc_713_, 3, v_contentLength_703_);
lean_ctor_set(v_reuseFailAlloc_713_, 4, v_body_704_);
v___x_709_ = v_reuseFailAlloc_713_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_711_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_709_);
v___x_711_ = v___x_698_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
lean_ctor_set_uint8(v_reuseFailAlloc_712_, sizeof(void*)*1, v_gated_695_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_660_);
return v_x_659_;
}
}
case 2:
{
uint8_t v_gated_718_; 
v_gated_718_ = lean_ctor_get_uint8(v_x_659_, sizeof(void*)*1);
if (v_gated_718_ == 0)
{
lean_object* v_c_719_; lean_object* v_code_720_; lean_object* v_wire_721_; uint8_t v___x_722_; 
v_c_719_ = lean_ctor_get(v_x_660_, 0);
lean_inc(v_c_719_);
v_code_720_ = lean_ctor_get(v_x_660_, 1);
lean_inc(v_code_720_);
lean_dec_ref(v_x_660_);
v_wire_721_ = lean_ctor_get(v_x_659_, 0);
lean_inc_ref(v_wire_721_);
v___x_722_ = lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_eval(v_c_719_, v_c_658_);
lean_dec(v_c_719_);
if (v___x_722_ == 0)
{
lean_dec_ref(v_wire_721_);
lean_dec(v_code_720_);
return v_x_659_;
}
else
{
lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_742_; 
v_isSharedCheck_742_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v_x_659_, 0);
lean_dec(v_unused_743_);
v___x_724_ = v_x_659_;
v_isShared_725_ = v_isSharedCheck_742_;
goto v_resetjp_723_;
}
else
{
lean_dec(v_x_659_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_742_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_headers_726_; lean_object* v_contentLength_727_; lean_object* v_body_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_739_; 
v_headers_726_ = lean_ctor_get(v_wire_721_, 2);
v_contentLength_727_ = lean_ctor_get(v_wire_721_, 3);
v_body_728_ = lean_ctor_get(v_wire_721_, 4);
v_isSharedCheck_739_ = !lean_is_exclusive(v_wire_721_);
if (v_isSharedCheck_739_ == 0)
{
lean_object* v_unused_740_; lean_object* v_unused_741_; 
v_unused_740_ = lean_ctor_get(v_wire_721_, 1);
lean_dec(v_unused_740_);
v_unused_741_ = lean_ctor_get(v_wire_721_, 0);
lean_dec(v_unused_741_);
v___x_730_ = v_wire_721_;
v_isShared_731_ = v_isSharedCheck_739_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_body_728_);
lean_inc(v_contentLength_727_);
lean_inc(v_headers_726_);
lean_dec(v_wire_721_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_739_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = lp_orb_x2dcompiler_Pancake_DslServe_reasonOf(v_code_720_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v___x_732_);
lean_ctor_set(v___x_730_, 0, v_code_720_);
v___x_734_ = v___x_730_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_code_720_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_headers_726_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v_contentLength_727_);
lean_ctor_set(v_reuseFailAlloc_738_, 4, v_body_728_);
v___x_734_ = v_reuseFailAlloc_738_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_736_; 
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_734_);
v___x_736_ = v___x_724_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_ctor_set_uint8(v___x_736_, sizeof(void*)*1, v___x_722_);
return v___x_736_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_x_660_);
lean_dec_ref(v_c_658_);
return v_x_659_;
}
}
case 3:
{
lean_object* v_wire_744_; lean_object* v_t_745_; uint8_t v_gated_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v_c_658_);
v_wire_744_ = lean_ctor_get(v_x_659_, 0);
lean_inc_ref(v_wire_744_);
v_t_745_ = lean_ctor_get(v_x_660_, 0);
lean_inc(v_t_745_);
lean_dec_ref(v_x_660_);
v_gated_746_ = lean_ctor_get_uint8(v_x_659_, sizeof(void*)*1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v_x_659_, 0);
lean_dec(v_unused_769_);
v___x_748_ = v_x_659_;
v_isShared_749_ = v_isSharedCheck_768_;
goto v_resetjp_747_;
}
else
{
lean_dec(v_x_659_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_768_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v_status_750_; lean_object* v_reason_751_; lean_object* v_headers_752_; lean_object* v_contentLength_753_; lean_object* v_body_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_767_; 
v_status_750_ = lean_ctor_get(v_wire_744_, 0);
v_reason_751_ = lean_ctor_get(v_wire_744_, 1);
v_headers_752_ = lean_ctor_get(v_wire_744_, 2);
v_contentLength_753_ = lean_ctor_get(v_wire_744_, 3);
v_body_754_ = lean_ctor_get(v_wire_744_, 4);
v_isSharedCheck_767_ = !lean_is_exclusive(v_wire_744_);
if (v_isSharedCheck_767_ == 0)
{
v___x_756_ = v_wire_744_;
v_isShared_757_ = v_isSharedCheck_767_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_body_754_);
lean_inc(v_contentLength_753_);
lean_inc(v_headers_752_);
lean_inc(v_reason_751_);
lean_inc(v_status_750_);
lean_dec(v_wire_744_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_767_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_758_ = l_List_lengthTR___redArg(v_t_745_);
v___x_759_ = lean_nat_add(v_contentLength_753_, v___x_758_);
lean_dec(v___x_758_);
lean_dec(v_contentLength_753_);
v___x_760_ = l_List_appendTR___redArg(v_body_754_, v_t_745_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v___x_760_);
lean_ctor_set(v___x_756_, 3, v___x_759_);
v___x_762_ = v___x_756_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_status_750_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_reason_751_);
lean_ctor_set(v_reuseFailAlloc_766_, 2, v_headers_752_);
lean_ctor_set(v_reuseFailAlloc_766_, 3, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_766_, 4, v___x_760_);
v___x_762_ = v_reuseFailAlloc_766_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_764_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_762_);
v___x_764_ = v___x_748_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, sizeof(void*)*1, v_gated_746_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
case 4:
{
lean_object* v_a_770_; lean_object* v_b_771_; lean_object* v___x_772_; 
v_a_770_ = lean_ctor_get(v_x_660_, 0);
lean_inc_ref(v_a_770_);
v_b_771_ = lean_ctor_get(v_x_660_, 1);
lean_inc_ref(v_b_771_);
lean_dec_ref(v_x_660_);
lean_inc_ref(v_c_658_);
v___x_772_ = lp_orb_x2dcompiler_Pancake_DslServe_compileStep(v_c_658_, v_x_659_, v_a_770_);
v_x_659_ = v___x_772_;
v_x_660_ = v_b_771_;
goto _start;
}
default: 
{
lean_object* v_c_774_; lean_object* v_a_775_; lean_object* v_b_776_; uint8_t v___x_777_; 
v_c_774_ = lean_ctor_get(v_x_660_, 0);
lean_inc(v_c_774_);
v_a_775_ = lean_ctor_get(v_x_660_, 1);
lean_inc_ref(v_a_775_);
v_b_776_ = lean_ctor_get(v_x_660_, 2);
lean_inc_ref(v_b_776_);
lean_dec_ref(v_x_660_);
lean_inc_ref(v_c_658_);
v___x_777_ = lp_orb_x2dcompiler_Pancake_DslServe_ReqPred_eval(v_c_774_, v_c_658_);
lean_dec(v_c_774_);
if (v___x_777_ == 0)
{
lean_dec_ref(v_a_775_);
v_x_660_ = v_b_776_;
goto _start;
}
else
{
lean_dec_ref(v_b_776_);
v_x_660_ = v_a_775_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_compileWire(lean_object* v_p_780_, lean_object* v_base_781_, lean_object* v_c_782_){
_start:
{
lean_object* v___x_783_; uint8_t v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v_wire_787_; 
v___x_783_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_build(v_base_781_);
v___x_784_ = 0;
v___x_785_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set_uint8(v___x_785_, sizeof(void*)*1, v___x_784_);
v___x_786_ = lp_orb_x2dcompiler_Pancake_DslServe_compileStep(v_c_782_, v___x_785_, v_p_780_);
v_wire_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc_ref(v_wire_787_);
lean_dec_ref(v___x_786_);
return v_wire_787_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_compileWire___boxed(lean_object* v_p_788_, lean_object* v_base_789_, lean_object* v_c_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = lp_orb_x2dcompiler_Pancake_DslServe_compileWire(v_p_788_, v_base_789_, v_c_790_);
lean_dec_ref(v_base_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_compile(lean_object* v_p_792_, lean_object* v_base_793_, lean_object* v_c_794_){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lp_orb_x2dcompiler_Pancake_DslServe_compileWire(v_p_792_, v_base_793_, v_c_794_);
v___x_796_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_serializeWire(v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_compile___boxed(lean_object* v_p_797_, lean_object* v_base_798_, lean_object* v_c_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = lp_orb_x2dcompiler_Pancake_DslServe_compile(v_p_797_, v_base_798_, v_c_799_);
lean_dec_ref(v_base_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_dToC(lean_object* v_dst_801_){
_start:
{
lean_object* v_resp_802_; uint8_t v_gated_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_811_; 
v_resp_802_ = lean_ctor_get(v_dst_801_, 0);
v_gated_803_ = lean_ctor_get_uint8(v_dst_801_, sizeof(void*)*1);
v_isSharedCheck_811_ = !lean_is_exclusive(v_dst_801_);
if (v_isSharedCheck_811_ == 0)
{
v___x_805_ = v_dst_801_;
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_resp_802_);
lean_dec(v_dst_801_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_build(v_resp_802_);
lean_dec_ref(v_resp_802_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_807_);
v___x_809_ = v___x_805_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
lean_ctor_set_uint8(v_reuseFailAlloc_810_, sizeof(void*)*1, v_gated_803_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_compileStep_match__1_splitter___redArg(lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_h__1_814_, lean_object* v_h__2_815_, lean_object* v_h__3_816_, lean_object* v_h__4_817_, lean_object* v_h__5_818_, lean_object* v_h__6_819_){
_start:
{
switch(lean_obj_tag(v_x_813_))
{
case 0:
{
lean_object* v_name_820_; lean_object* v_val_821_; lean_object* v___x_822_; 
lean_dec(v_h__6_819_);
lean_dec(v_h__5_818_);
lean_dec(v_h__4_817_);
lean_dec(v_h__3_816_);
lean_dec(v_h__2_815_);
v_name_820_ = lean_ctor_get(v_x_813_, 0);
lean_inc(v_name_820_);
v_val_821_ = lean_ctor_get(v_x_813_, 1);
lean_inc(v_val_821_);
lean_dec_ref(v_x_813_);
v___x_822_ = lean_apply_3(v_h__1_814_, v_x_812_, v_name_820_, v_val_821_);
return v___x_822_;
}
case 1:
{
lean_object* v_code_823_; lean_object* v_reason_824_; lean_object* v___x_825_; 
lean_dec(v_h__6_819_);
lean_dec(v_h__5_818_);
lean_dec(v_h__4_817_);
lean_dec(v_h__3_816_);
lean_dec(v_h__1_814_);
v_code_823_ = lean_ctor_get(v_x_813_, 0);
lean_inc(v_code_823_);
v_reason_824_ = lean_ctor_get(v_x_813_, 1);
lean_inc(v_reason_824_);
lean_dec_ref(v_x_813_);
v___x_825_ = lean_apply_3(v_h__2_815_, v_x_812_, v_code_823_, v_reason_824_);
return v___x_825_;
}
case 2:
{
lean_object* v_c_826_; lean_object* v_code_827_; lean_object* v___x_828_; 
lean_dec(v_h__6_819_);
lean_dec(v_h__5_818_);
lean_dec(v_h__4_817_);
lean_dec(v_h__2_815_);
lean_dec(v_h__1_814_);
v_c_826_ = lean_ctor_get(v_x_813_, 0);
lean_inc(v_c_826_);
v_code_827_ = lean_ctor_get(v_x_813_, 1);
lean_inc(v_code_827_);
lean_dec_ref(v_x_813_);
v___x_828_ = lean_apply_3(v_h__3_816_, v_x_812_, v_c_826_, v_code_827_);
return v___x_828_;
}
case 3:
{
lean_object* v_t_829_; lean_object* v___x_830_; 
lean_dec(v_h__6_819_);
lean_dec(v_h__5_818_);
lean_dec(v_h__3_816_);
lean_dec(v_h__2_815_);
lean_dec(v_h__1_814_);
v_t_829_ = lean_ctor_get(v_x_813_, 0);
lean_inc(v_t_829_);
lean_dec_ref(v_x_813_);
v___x_830_ = lean_apply_2(v_h__4_817_, v_x_812_, v_t_829_);
return v___x_830_;
}
case 4:
{
lean_object* v_a_831_; lean_object* v_b_832_; lean_object* v___x_833_; 
lean_dec(v_h__6_819_);
lean_dec(v_h__4_817_);
lean_dec(v_h__3_816_);
lean_dec(v_h__2_815_);
lean_dec(v_h__1_814_);
v_a_831_ = lean_ctor_get(v_x_813_, 0);
lean_inc_ref(v_a_831_);
v_b_832_ = lean_ctor_get(v_x_813_, 1);
lean_inc_ref(v_b_832_);
lean_dec_ref(v_x_813_);
v___x_833_ = lean_apply_3(v_h__5_818_, v_x_812_, v_a_831_, v_b_832_);
return v___x_833_;
}
default: 
{
lean_object* v_c_834_; lean_object* v_a_835_; lean_object* v_b_836_; lean_object* v___x_837_; 
lean_dec(v_h__5_818_);
lean_dec(v_h__4_817_);
lean_dec(v_h__3_816_);
lean_dec(v_h__2_815_);
lean_dec(v_h__1_814_);
v_c_834_ = lean_ctor_get(v_x_813_, 0);
lean_inc(v_c_834_);
v_a_835_ = lean_ctor_get(v_x_813_, 1);
lean_inc_ref(v_a_835_);
v_b_836_ = lean_ctor_get(v_x_813_, 2);
lean_inc_ref(v_b_836_);
lean_dec_ref(v_x_813_);
v___x_837_ = lean_apply_4(v_h__6_819_, v_x_812_, v_c_834_, v_a_835_, v_b_836_);
return v___x_837_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_compileStep_match__1_splitter(lean_object* v_motive_838_, lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v_h__1_841_, lean_object* v_h__2_842_, lean_object* v_h__3_843_, lean_object* v_h__4_844_, lean_object* v_h__5_845_, lean_object* v_h__6_846_){
_start:
{
switch(lean_obj_tag(v_x_840_))
{
case 0:
{
lean_object* v_name_847_; lean_object* v_val_848_; lean_object* v___x_849_; 
lean_dec(v_h__6_846_);
lean_dec(v_h__5_845_);
lean_dec(v_h__4_844_);
lean_dec(v_h__3_843_);
lean_dec(v_h__2_842_);
v_name_847_ = lean_ctor_get(v_x_840_, 0);
lean_inc(v_name_847_);
v_val_848_ = lean_ctor_get(v_x_840_, 1);
lean_inc(v_val_848_);
lean_dec_ref(v_x_840_);
v___x_849_ = lean_apply_3(v_h__1_841_, v_x_839_, v_name_847_, v_val_848_);
return v___x_849_;
}
case 1:
{
lean_object* v_code_850_; lean_object* v_reason_851_; lean_object* v___x_852_; 
lean_dec(v_h__6_846_);
lean_dec(v_h__5_845_);
lean_dec(v_h__4_844_);
lean_dec(v_h__3_843_);
lean_dec(v_h__1_841_);
v_code_850_ = lean_ctor_get(v_x_840_, 0);
lean_inc(v_code_850_);
v_reason_851_ = lean_ctor_get(v_x_840_, 1);
lean_inc(v_reason_851_);
lean_dec_ref(v_x_840_);
v___x_852_ = lean_apply_3(v_h__2_842_, v_x_839_, v_code_850_, v_reason_851_);
return v___x_852_;
}
case 2:
{
lean_object* v_c_853_; lean_object* v_code_854_; lean_object* v___x_855_; 
lean_dec(v_h__6_846_);
lean_dec(v_h__5_845_);
lean_dec(v_h__4_844_);
lean_dec(v_h__2_842_);
lean_dec(v_h__1_841_);
v_c_853_ = lean_ctor_get(v_x_840_, 0);
lean_inc(v_c_853_);
v_code_854_ = lean_ctor_get(v_x_840_, 1);
lean_inc(v_code_854_);
lean_dec_ref(v_x_840_);
v___x_855_ = lean_apply_3(v_h__3_843_, v_x_839_, v_c_853_, v_code_854_);
return v___x_855_;
}
case 3:
{
lean_object* v_t_856_; lean_object* v___x_857_; 
lean_dec(v_h__6_846_);
lean_dec(v_h__5_845_);
lean_dec(v_h__3_843_);
lean_dec(v_h__2_842_);
lean_dec(v_h__1_841_);
v_t_856_ = lean_ctor_get(v_x_840_, 0);
lean_inc(v_t_856_);
lean_dec_ref(v_x_840_);
v___x_857_ = lean_apply_2(v_h__4_844_, v_x_839_, v_t_856_);
return v___x_857_;
}
case 4:
{
lean_object* v_a_858_; lean_object* v_b_859_; lean_object* v___x_860_; 
lean_dec(v_h__6_846_);
lean_dec(v_h__4_844_);
lean_dec(v_h__3_843_);
lean_dec(v_h__2_842_);
lean_dec(v_h__1_841_);
v_a_858_ = lean_ctor_get(v_x_840_, 0);
lean_inc_ref(v_a_858_);
v_b_859_ = lean_ctor_get(v_x_840_, 1);
lean_inc_ref(v_b_859_);
lean_dec_ref(v_x_840_);
v___x_860_ = lean_apply_3(v_h__5_845_, v_x_839_, v_a_858_, v_b_859_);
return v___x_860_;
}
default: 
{
lean_object* v_c_861_; lean_object* v_a_862_; lean_object* v_b_863_; lean_object* v___x_864_; 
lean_dec(v_h__5_845_);
lean_dec(v_h__4_844_);
lean_dec(v_h__3_843_);
lean_dec(v_h__2_842_);
lean_dec(v_h__1_841_);
v_c_861_ = lean_ctor_get(v_x_840_, 0);
lean_inc(v_c_861_);
v_a_862_ = lean_ctor_get(v_x_840_, 1);
lean_inc_ref(v_a_862_);
v_b_863_ = lean_ctor_get(v_x_840_, 2);
lean_inc_ref(v_b_863_);
lean_dec_ref(v_x_840_);
v___x_864_ = lean_apply_4(v_h__6_846_, v_x_839_, v_c_861_, v_a_862_, v_b_863_);
return v___x_864_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_denoteStep_match__1_splitter___redArg(lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_h__1_867_, lean_object* v_h__2_868_, lean_object* v_h__3_869_, lean_object* v_h__4_870_, lean_object* v_h__5_871_, lean_object* v_h__6_872_){
_start:
{
switch(lean_obj_tag(v_x_866_))
{
case 0:
{
lean_object* v_name_873_; lean_object* v_val_874_; lean_object* v___x_875_; 
lean_dec(v_h__6_872_);
lean_dec(v_h__5_871_);
lean_dec(v_h__4_870_);
lean_dec(v_h__3_869_);
lean_dec(v_h__2_868_);
v_name_873_ = lean_ctor_get(v_x_866_, 0);
lean_inc(v_name_873_);
v_val_874_ = lean_ctor_get(v_x_866_, 1);
lean_inc(v_val_874_);
lean_dec_ref(v_x_866_);
v___x_875_ = lean_apply_3(v_h__1_867_, v_x_865_, v_name_873_, v_val_874_);
return v___x_875_;
}
case 1:
{
lean_object* v_code_876_; lean_object* v_reason_877_; lean_object* v___x_878_; 
lean_dec(v_h__6_872_);
lean_dec(v_h__5_871_);
lean_dec(v_h__4_870_);
lean_dec(v_h__3_869_);
lean_dec(v_h__1_867_);
v_code_876_ = lean_ctor_get(v_x_866_, 0);
lean_inc(v_code_876_);
v_reason_877_ = lean_ctor_get(v_x_866_, 1);
lean_inc(v_reason_877_);
lean_dec_ref(v_x_866_);
v___x_878_ = lean_apply_3(v_h__2_868_, v_x_865_, v_code_876_, v_reason_877_);
return v___x_878_;
}
case 2:
{
lean_object* v_c_879_; lean_object* v_code_880_; lean_object* v___x_881_; 
lean_dec(v_h__6_872_);
lean_dec(v_h__5_871_);
lean_dec(v_h__4_870_);
lean_dec(v_h__2_868_);
lean_dec(v_h__1_867_);
v_c_879_ = lean_ctor_get(v_x_866_, 0);
lean_inc(v_c_879_);
v_code_880_ = lean_ctor_get(v_x_866_, 1);
lean_inc(v_code_880_);
lean_dec_ref(v_x_866_);
v___x_881_ = lean_apply_3(v_h__3_869_, v_x_865_, v_c_879_, v_code_880_);
return v___x_881_;
}
case 3:
{
lean_object* v_t_882_; lean_object* v___x_883_; 
lean_dec(v_h__6_872_);
lean_dec(v_h__5_871_);
lean_dec(v_h__3_869_);
lean_dec(v_h__2_868_);
lean_dec(v_h__1_867_);
v_t_882_ = lean_ctor_get(v_x_866_, 0);
lean_inc(v_t_882_);
lean_dec_ref(v_x_866_);
v___x_883_ = lean_apply_2(v_h__4_870_, v_x_865_, v_t_882_);
return v___x_883_;
}
case 4:
{
lean_object* v_a_884_; lean_object* v_b_885_; lean_object* v___x_886_; 
lean_dec(v_h__6_872_);
lean_dec(v_h__4_870_);
lean_dec(v_h__3_869_);
lean_dec(v_h__2_868_);
lean_dec(v_h__1_867_);
v_a_884_ = lean_ctor_get(v_x_866_, 0);
lean_inc_ref(v_a_884_);
v_b_885_ = lean_ctor_get(v_x_866_, 1);
lean_inc_ref(v_b_885_);
lean_dec_ref(v_x_866_);
v___x_886_ = lean_apply_3(v_h__5_871_, v_x_865_, v_a_884_, v_b_885_);
return v___x_886_;
}
default: 
{
lean_object* v_c_887_; lean_object* v_a_888_; lean_object* v_b_889_; lean_object* v___x_890_; 
lean_dec(v_h__5_871_);
lean_dec(v_h__4_870_);
lean_dec(v_h__3_869_);
lean_dec(v_h__2_868_);
lean_dec(v_h__1_867_);
v_c_887_ = lean_ctor_get(v_x_866_, 0);
lean_inc(v_c_887_);
v_a_888_ = lean_ctor_get(v_x_866_, 1);
lean_inc_ref(v_a_888_);
v_b_889_ = lean_ctor_get(v_x_866_, 2);
lean_inc_ref(v_b_889_);
lean_dec_ref(v_x_866_);
v___x_890_ = lean_apply_4(v_h__6_872_, v_x_865_, v_c_887_, v_a_888_, v_b_889_);
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_DslServe_0__Pancake_DslServe_denoteStep_match__1_splitter(lean_object* v_motive_891_, lean_object* v_x_892_, lean_object* v_x_893_, lean_object* v_h__1_894_, lean_object* v_h__2_895_, lean_object* v_h__3_896_, lean_object* v_h__4_897_, lean_object* v_h__5_898_, lean_object* v_h__6_899_){
_start:
{
switch(lean_obj_tag(v_x_893_))
{
case 0:
{
lean_object* v_name_900_; lean_object* v_val_901_; lean_object* v___x_902_; 
lean_dec(v_h__6_899_);
lean_dec(v_h__5_898_);
lean_dec(v_h__4_897_);
lean_dec(v_h__3_896_);
lean_dec(v_h__2_895_);
v_name_900_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_name_900_);
v_val_901_ = lean_ctor_get(v_x_893_, 1);
lean_inc(v_val_901_);
lean_dec_ref(v_x_893_);
v___x_902_ = lean_apply_3(v_h__1_894_, v_x_892_, v_name_900_, v_val_901_);
return v___x_902_;
}
case 1:
{
lean_object* v_code_903_; lean_object* v_reason_904_; lean_object* v___x_905_; 
lean_dec(v_h__6_899_);
lean_dec(v_h__5_898_);
lean_dec(v_h__4_897_);
lean_dec(v_h__3_896_);
lean_dec(v_h__1_894_);
v_code_903_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_code_903_);
v_reason_904_ = lean_ctor_get(v_x_893_, 1);
lean_inc(v_reason_904_);
lean_dec_ref(v_x_893_);
v___x_905_ = lean_apply_3(v_h__2_895_, v_x_892_, v_code_903_, v_reason_904_);
return v___x_905_;
}
case 2:
{
lean_object* v_c_906_; lean_object* v_code_907_; lean_object* v___x_908_; 
lean_dec(v_h__6_899_);
lean_dec(v_h__5_898_);
lean_dec(v_h__4_897_);
lean_dec(v_h__2_895_);
lean_dec(v_h__1_894_);
v_c_906_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_c_906_);
v_code_907_ = lean_ctor_get(v_x_893_, 1);
lean_inc(v_code_907_);
lean_dec_ref(v_x_893_);
v___x_908_ = lean_apply_3(v_h__3_896_, v_x_892_, v_c_906_, v_code_907_);
return v___x_908_;
}
case 3:
{
lean_object* v_t_909_; lean_object* v___x_910_; 
lean_dec(v_h__6_899_);
lean_dec(v_h__5_898_);
lean_dec(v_h__3_896_);
lean_dec(v_h__2_895_);
lean_dec(v_h__1_894_);
v_t_909_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_t_909_);
lean_dec_ref(v_x_893_);
v___x_910_ = lean_apply_2(v_h__4_897_, v_x_892_, v_t_909_);
return v___x_910_;
}
case 4:
{
lean_object* v_a_911_; lean_object* v_b_912_; lean_object* v___x_913_; 
lean_dec(v_h__6_899_);
lean_dec(v_h__4_897_);
lean_dec(v_h__3_896_);
lean_dec(v_h__2_895_);
lean_dec(v_h__1_894_);
v_a_911_ = lean_ctor_get(v_x_893_, 0);
lean_inc_ref(v_a_911_);
v_b_912_ = lean_ctor_get(v_x_893_, 1);
lean_inc_ref(v_b_912_);
lean_dec_ref(v_x_893_);
v___x_913_ = lean_apply_3(v_h__5_898_, v_x_892_, v_a_911_, v_b_912_);
return v___x_913_;
}
default: 
{
lean_object* v_c_914_; lean_object* v_a_915_; lean_object* v_b_916_; lean_object* v___x_917_; 
lean_dec(v_h__5_898_);
lean_dec(v_h__4_897_);
lean_dec(v_h__3_896_);
lean_dec(v_h__2_895_);
lean_dec(v_h__1_894_);
v_c_914_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_c_914_);
v_a_915_ = lean_ctor_get(v_x_893_, 1);
lean_inc_ref(v_a_915_);
v_b_916_ = lean_ctor_get(v_x_893_, 2);
lean_inc_ref(v_b_916_);
lean_dec_ref(v_x_893_);
v___x_917_ = lean_apply_4(v_h__6_899_, v_x_892_, v_c_914_, v_a_915_, v_b_916_);
return v___x_917_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_DslServe_seqAddHeaders(lean_object* v_x_924_){
_start:
{
if (lean_obj_tag(v_x_924_) == 0)
{
lean_object* v___x_925_; 
v___x_925_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_seqAddHeaders___closed__0));
return v___x_925_;
}
else
{
lean_object* v_tail_926_; 
v_tail_926_ = lean_ctor_get(v_x_924_, 1);
if (lean_obj_tag(v_tail_926_) == 0)
{
lean_object* v_head_927_; lean_object* v_fst_928_; lean_object* v_snd_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
v_head_927_ = lean_ctor_get(v_x_924_, 0);
lean_inc(v_head_927_);
lean_dec_ref(v_x_924_);
v_fst_928_ = lean_ctor_get(v_head_927_, 0);
v_snd_929_ = lean_ctor_get(v_head_927_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_head_927_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v_head_927_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_snd_929_);
lean_inc(v_fst_928_);
lean_dec(v_head_927_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_fst_928_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_snd_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
else
{
lean_object* v_head_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_954_; 
lean_inc(v_tail_926_);
v_head_937_ = lean_ctor_get(v_x_924_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v_x_924_);
if (v_isSharedCheck_954_ == 0)
{
lean_object* v_unused_955_; 
v_unused_955_ = lean_ctor_get(v_x_924_, 1);
lean_dec(v_unused_955_);
v___x_939_ = v_x_924_;
v_isShared_940_ = v_isSharedCheck_954_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_head_937_);
lean_dec(v_x_924_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_954_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_fst_941_; lean_object* v_snd_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_953_; 
v_fst_941_ = lean_ctor_get(v_head_937_, 0);
v_snd_942_ = lean_ctor_get(v_head_937_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v_head_937_);
if (v_isSharedCheck_953_ == 0)
{
v___x_944_ = v_head_937_;
v_isShared_945_ = v_isSharedCheck_953_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_snd_942_);
lean_inc(v_fst_941_);
lean_dec(v_head_937_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_953_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_fst_941_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_snd_942_);
v___x_947_ = v_reuseFailAlloc_952_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_948_ = lp_orb_x2dcompiler_Pancake_DslServe_seqAddHeaders(v_tail_926_);
if (v_isShared_940_ == 0)
{
lean_ctor_set_tag(v___x_939_, 4);
lean_ctor_set(v___x_939_, 1, v___x_948_);
lean_ctor_set(v___x_939_, 0, v___x_947_);
v___x_950_ = v___x_939_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
}
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__0(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders;
v___x_957_ = lp_orb_x2dcompiler_Pancake_DslServe_seqAddHeaders(v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__1(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__3, &lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__3);
v___x_959_ = lean_unsigned_to_nat(200u);
v___x_960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v___x_958_);
return v___x_960_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__3(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__2));
v___x_963_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__4(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__3, &lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__3);
v___x_965_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__5(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_966_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__4, &lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__4);
v___x_967_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__1, &lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__1);
v___x_968_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_966_);
return v___x_968_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__6(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_969_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__5, &lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__5);
v___x_970_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__0, &lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__0);
v___x_971_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v___x_969_);
return v___x_971_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_okStage(void){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__6, &lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__6);
return v___x_972_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__1(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__0));
v___x_975_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__3(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__2));
v___x_978_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__4(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__3, &lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__3);
v___x_980_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__1, &lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__1);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_979_);
return v___x_981_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__5(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__7, &lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_reasonOf___closed__7);
v___x_983_ = lean_unsigned_to_nat(405u);
v___x_984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v___x_982_);
return v___x_984_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__7(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__6));
v___x_987_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__8(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__7, &lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__7);
v___x_989_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__9(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__8, &lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__8);
v___x_991_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__5, &lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__5);
v___x_992_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_990_);
return v___x_992_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__10(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__9, &lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__9);
v___x_994_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__0, &lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_okStage___closed__0);
v___x_995_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_993_);
return v___x_995_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__11(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__10, &lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__10);
v___x_997_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__4, &lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__4);
v___x_998_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v___x_996_);
return v___x_998_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage(void){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__11, &lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage___closed__11);
return v___x_999_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__2(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1005_ = lp_orb_x2dcompiler_Pancake_DslServe_okStage;
v___x_1006_ = lp_orb_x2dcompiler_Pancake_DslServe_refuseStage;
v___x_1007_ = lean_box(0);
v___x_1008_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_1006_);
lean_ctor_set(v___x_1008_, 2, v___x_1005_);
return v___x_1008_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__3(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__2, &lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__2);
v___x_1010_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__1));
v___x_1011_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_1009_);
return v___x_1011_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_DslServe_serveProg(void){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__3, &lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_DslServe_serveProg___closed__3);
return v___x_1012_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_ServeSlice(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_DslServe(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_ServeSlice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Pancake_DslServe_okStage = _init_lp_orb_x2dcompiler_Pancake_DslServe_okStage();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_DslServe_okStage);
lp_orb_x2dcompiler_Pancake_DslServe_refuseStage = _init_lp_orb_x2dcompiler_Pancake_DslServe_refuseStage();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_DslServe_refuseStage);
lp_orb_x2dcompiler_Pancake_DslServe_serveProg = _init_lp_orb_x2dcompiler_Pancake_DslServe_serveProg();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_DslServe_serveProg);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
