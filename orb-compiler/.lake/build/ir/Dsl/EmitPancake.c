// Lean compiler output
// Module: Dsl.EmitPancake
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern uint8_t l_instInhabitedUInt8;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_add_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_add_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_add_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_add_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_mul_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_mul_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_mul_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_mul_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_lt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_lt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_lt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_lt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_and___00elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_and___00elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_and___00elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_and___00elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_eq_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_eq_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_eq_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_eq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_le_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_le_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_le_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_le_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_sub_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_sub_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_sub_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_sub_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Dsl_EmitPancake_instDecidableEqPOp(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instDecidableEqPOp___boxed(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Dsl.EmitPancake.POp.add"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Dsl.EmitPancake.POp.mul"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Dsl.EmitPancake.POp.lt"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__4_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__5_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Dsl.EmitPancake.POp.and_"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__6_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__7_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Dsl.EmitPancake.POp.eq"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__9_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Dsl.EmitPancake.POp.le"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__10_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__10_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__11_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Dsl.EmitPancake.POp.sub"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__12_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__12_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__13_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_base_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_base_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_const_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_binop_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_binop_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_loadw_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_loadw_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_loadb_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_loadb_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Dsl.EmitPancake.PExpr.base"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Dsl.EmitPancake.PExpr.const"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__4_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Dsl.EmitPancake.PExpr.var"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__7_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Dsl.EmitPancake.PExpr.binop"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__10_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Dsl.EmitPancake.PExpr.loadw"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__11_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__11_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__12_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__13_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Dsl.EmitPancake.PExpr.loadb"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__14_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__14_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__15 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__15_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__16 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__16_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_dec_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_dec_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_assign_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_assign_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_store_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_store_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_storeb_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_storeb_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ffi_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ffi_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_call_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_call_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ret_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ret_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ite_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ite_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_while_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_while_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__2_value;
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__5_value;
static const lean_string_object lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__10_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Dsl.EmitPancake.PStmt.dec"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__2_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Dsl.EmitPancake.PStmt.assign"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__3_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__5_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Dsl.EmitPancake.PStmt.store"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__6_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__7_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__8_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Dsl.EmitPancake.PStmt.storeb"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__9_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__10_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__11_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Dsl.EmitPancake.PStmt.ffi"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__12_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__12_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__13_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__14_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Dsl.EmitPancake.PStmt.call"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__15 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__15_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__15_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__16 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__16_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__16_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__17 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__17_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Dsl.EmitPancake.PStmt.ret"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__18 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__18_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__18_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__19 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__19_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__19_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__20 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__20_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Dsl.EmitPancake.PStmt.ite"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__21 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__21_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__21_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__22 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__22_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__22_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__23 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__23_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1___redArg(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Dsl.EmitPancake.PStmt.while"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__24 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__24_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__24_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__25 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__25_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__25_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__26 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__26_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__1___redArg(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__3;
static const lean_ctor_object lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__1_value)}};
static const lean_object* lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0___redArg(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__1_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__4_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__3_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__6_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__7;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "params"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__9_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__10;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "body"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__11_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__11_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__12_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "exported"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__13_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__13_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__14_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__15;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__16 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__16_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__17;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__18;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__19 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__19_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__16_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__20 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__20_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__2_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "&"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=="};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__4_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "<="};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__5_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__6_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_opSym(uint8_t);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Dsl_EmitPancake_isAssoc(uint8_t);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_isAssoc___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_wrapOperand(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_wrapOperand___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_wrapAtom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_wrapAtom___boxed(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "@base"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lds "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__2_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ld8 "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__3_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_ppStmt_spec__0(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "var "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " = "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__2_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "st "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__4_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "st8 "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__5_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__6_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ");"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__7_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "return "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__8_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "if "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__9_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " {"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__10_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__11_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "} else {"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__12_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__13_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "while "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__14_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmts(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_ppFun_spec__0(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ") {"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__2_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fun "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "export fun "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__4_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_sCall(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_isCall(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_isCall___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eMul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eAnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eLe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eSub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_v(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_n(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "load_vec"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "report_vec"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__3;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "base"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "buf"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__4_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "alen"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__5_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "off"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__6_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "len"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__7_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__8_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__9_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__10_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__11_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__6_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__12_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__7_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__13_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__14;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__15;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "acc"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__16 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__16_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__16_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__9_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__17 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__17_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__18 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__18_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__18_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__9_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__19 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__19_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__18_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__20 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__20_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__21;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__16_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__22 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__22_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__23;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__24;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__25;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__26 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__26_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__27;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__28;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__29;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__8_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__22_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__30 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__30_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__31 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__31_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__32 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__32_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(8) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__33 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__33_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__33_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__34 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__34_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__3_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__34_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__35 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__35_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__33_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__35_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__36 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__36_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__9_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__37 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__37_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__38 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__38_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ctrl"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__7_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "out"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__4_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__3_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__6_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__7_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__2_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__7_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__1_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__10_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__4_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__11_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__11_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__32_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__12_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__32_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__13_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__14_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__12_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__14_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__15 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__15_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_boundscanExport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "boundscan"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_boundscanExport___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_boundscanExport___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_boundscanExport;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_machineC0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*9 + 0, .m_other = 9, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__0_value),((lean_object*)(((size_t)(16) << 1) | 1)),((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(4096) << 1) | 1)),((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__1_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_machineC0___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_machineC0___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_machineC0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_machineC0___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "found"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__0_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__9_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__4;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__5_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__6;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__8;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__0_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__26_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__10_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__11_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__8_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__20_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__12_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_firstBelow(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_firstBelow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_tokenScanSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_tokenScanSpec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0___redArg(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "funs"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__1_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__2_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__3_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_ppProgram_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppProgram(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "resp"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__2_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__1_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__3_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__4_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__7_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__5_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__7_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__9_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__10;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__11;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__12;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__7_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__13_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__14_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage(lean_object*);
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "admit"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__1_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__4_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_emitServeMain_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Dsl_EmitPancake_emitServeMain_spec__3(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_emitServeMain_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_emitServeMain_spec__2___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_emitServeMain_spec__2___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_emitServeMain_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_emitServeMain_spec__1(lean_object*, lean_object*);
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitServeMain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitServeMain___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitServeMain___closed__0_value;
static const lean_array_object lp_orb_x2dcompiler_Dsl_EmitPancake_emitServeMain___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitServeMain___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitServeMain___closed__1_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitServeMain(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_fuse_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_fuse_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_fuse(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "load_serve"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "report_serve"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(200) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(16) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(40) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__7_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(56) << 1) | 1)),((lean_object*)(((size_t)(159) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(64) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__10_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(72) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__11_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(80) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__12_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__13_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__11_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__13_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__14_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__10_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__14_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__15 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__15_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__9_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__15_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__16 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__16_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__8_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__16_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__17 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__17_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__7_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__17_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__18 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__18_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__6_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__18_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__19 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__19_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__5_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__19_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__20 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__20_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__4_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__20_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__21 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__21_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__3_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__21_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__22 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__22_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__2_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__22_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__23 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__23_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(64) << 1) | 1)),((lean_object*)(((size_t)(16) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__24 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__24_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(72) << 1) | 1)),((lean_object*)(((size_t)(72) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__25 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__25_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(80) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__26 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__26_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(88) << 1) | 1)),((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__27 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__27_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(96) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__28 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__28_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(104) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__29 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__29_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__30 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__30_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__28_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__30_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__31 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__31_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__27_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__31_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__32 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__32_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__26_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__32_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__33 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__33_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__25_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__33_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__34 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__34_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__24_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__34_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__35 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__35_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*11 + 0, .m_other = 11, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__0_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__1_value),((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(4096) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2048) << 1) | 1)),((lean_object*)(((size_t)(4096) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(80) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__23_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__35_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__36 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__36_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "machine_stage"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__37 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__37_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__37_value),((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(128) << 1) | 1)),((lean_object*)(((size_t)(255) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__38 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__38_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__39;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "counter"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__40 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__40_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__41 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__41_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__4_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__41_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__42 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__42_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__6_value),((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__42_value)}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__43 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__43_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__44;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "admit_combine"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__45 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__45_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__45_value),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(80) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__46 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__46_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__47;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fin"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__48 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__48_value;
static const lean_ctor_object lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__49 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__49_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__50;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__51;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__52;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__53;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_banner___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "// GENERATED by Dsl/EmitPancake.lean -- do not hand-edit.\n// "};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_banner___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_banner___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_banner___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "// Emission is generative: this file is ppFun applied to the primitive spec.\n\n"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_banner___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_banner___closed__1_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_banner(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_banner___boxed(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "region primitive (bounds-check + byte-scan) -- reproduces C0 boundscan.pnk"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "machine primitive (guarded threshold token scan) -- Link A scaffolded"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "region stage as a C-callable export fun (SysV ABI: ctrl/buf/len/out) -- no FFI, no main"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__3;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 124, .m_capacity = 124, .m_length = 123, .m_data = "fused serve SLICE (machine_stage + admit_combine) -- GENERATED entry sequences the stage calls (multi-function, PStmt.call)"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__3;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_IO_print___at___00IO_println___at___00Dsl_EmitPancake_main_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_IO_print___at___00IO_println___at___00Dsl_EmitPancake_main_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_IO_println___at___00Dsl_EmitPancake_main_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_IO_println___at___00Dsl_EmitPancake_main_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "docs/engine/probes/compiler/emit/region.pnk"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "docs/engine/probes/compiler/emit/machine.pnk"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "docs/engine/probes/compiler/emit/serve_slice.pnk"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__2_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "docs/engine/probes/compiler/emit/boundscan_export.pnk"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "wrote emit/region.pnk, emit/machine.pnk, emit/serve_slice.pnk and emit/boundscan_export.pnk"};
static const lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__4_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_main();
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_main___boxed(lean_object*);
LEAN_EXPORT lean_object* _lean_main();
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_main___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
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
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
default: 
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorIdx___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_boxed_10_; lean_object* v_res_11_; 
v_x_boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorIdx(v_x_boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_toCtorIdx(uint8_t v_x_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorIdx(v_x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_toCtorIdx___boxed(lean_object* v_x_14_){
_start:
{
uint8_t v_x_4__boxed_15_; lean_object* v_res_16_; 
v_x_4__boxed_15_ = lean_unbox(v_x_14_);
v_res_16_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_toCtorIdx(v_x_4__boxed_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorElim___redArg(lean_object* v_k_17_){
_start:
{
lean_inc(v_k_17_);
return v_k_17_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorElim___redArg___boxed(lean_object* v_k_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorElim___redArg(v_k_18_);
lean_dec(v_k_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorElim(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, uint8_t v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_inc(v_k_24_);
return v_k_24_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorElim___boxed(lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
uint8_t v_t_boxed_30_; lean_object* v_res_31_; 
v_t_boxed_30_ = lean_unbox(v_t_27_);
v_res_31_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorElim(v_motive_25_, v_ctorIdx_26_, v_t_boxed_30_, v_h_28_, v_k_29_);
lean_dec(v_k_29_);
lean_dec(v_ctorIdx_26_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_add_elim___redArg(lean_object* v_add_32_){
_start:
{
lean_inc(v_add_32_);
return v_add_32_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_add_elim___redArg___boxed(lean_object* v_add_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_add_elim___redArg(v_add_33_);
lean_dec(v_add_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_add_elim(lean_object* v_motive_35_, uint8_t v_t_36_, lean_object* v_h_37_, lean_object* v_add_38_){
_start:
{
lean_inc(v_add_38_);
return v_add_38_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_add_elim___boxed(lean_object* v_motive_39_, lean_object* v_t_40_, lean_object* v_h_41_, lean_object* v_add_42_){
_start:
{
uint8_t v_t_boxed_43_; lean_object* v_res_44_; 
v_t_boxed_43_ = lean_unbox(v_t_40_);
v_res_44_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_add_elim(v_motive_39_, v_t_boxed_43_, v_h_41_, v_add_42_);
lean_dec(v_add_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_mul_elim___redArg(lean_object* v_mul_45_){
_start:
{
lean_inc(v_mul_45_);
return v_mul_45_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_mul_elim___redArg___boxed(lean_object* v_mul_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_mul_elim___redArg(v_mul_46_);
lean_dec(v_mul_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_mul_elim(lean_object* v_motive_48_, uint8_t v_t_49_, lean_object* v_h_50_, lean_object* v_mul_51_){
_start:
{
lean_inc(v_mul_51_);
return v_mul_51_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_mul_elim___boxed(lean_object* v_motive_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_mul_55_){
_start:
{
uint8_t v_t_boxed_56_; lean_object* v_res_57_; 
v_t_boxed_56_ = lean_unbox(v_t_53_);
v_res_57_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_mul_elim(v_motive_52_, v_t_boxed_56_, v_h_54_, v_mul_55_);
lean_dec(v_mul_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_lt_elim___redArg(lean_object* v_lt_58_){
_start:
{
lean_inc(v_lt_58_);
return v_lt_58_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_lt_elim___redArg___boxed(lean_object* v_lt_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_lt_elim___redArg(v_lt_59_);
lean_dec(v_lt_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_lt_elim(lean_object* v_motive_61_, uint8_t v_t_62_, lean_object* v_h_63_, lean_object* v_lt_64_){
_start:
{
lean_inc(v_lt_64_);
return v_lt_64_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_lt_elim___boxed(lean_object* v_motive_65_, lean_object* v_t_66_, lean_object* v_h_67_, lean_object* v_lt_68_){
_start:
{
uint8_t v_t_boxed_69_; lean_object* v_res_70_; 
v_t_boxed_69_ = lean_unbox(v_t_66_);
v_res_70_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_lt_elim(v_motive_65_, v_t_boxed_69_, v_h_67_, v_lt_68_);
lean_dec(v_lt_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_and___00elim___redArg(lean_object* v_and___71_){
_start:
{
lean_inc(v_and___71_);
return v_and___71_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_and___00elim___redArg___boxed(lean_object* v_and___72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_and___00elim___redArg(v_and___72_);
lean_dec(v_and___72_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_and___00elim(lean_object* v_motive_74_, uint8_t v_t_75_, lean_object* v_h_76_, lean_object* v_and___77_){
_start:
{
lean_inc(v_and___77_);
return v_and___77_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_and___00elim___boxed(lean_object* v_motive_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_and___81_){
_start:
{
uint8_t v_t_boxed_82_; lean_object* v_res_83_; 
v_t_boxed_82_ = lean_unbox(v_t_79_);
v_res_83_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_and___00elim(v_motive_78_, v_t_boxed_82_, v_h_80_, v_and___81_);
lean_dec(v_and___81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_eq_elim___redArg(lean_object* v_eq_84_){
_start:
{
lean_inc(v_eq_84_);
return v_eq_84_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_eq_elim___redArg___boxed(lean_object* v_eq_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_eq_elim___redArg(v_eq_85_);
lean_dec(v_eq_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_eq_elim(lean_object* v_motive_87_, uint8_t v_t_88_, lean_object* v_h_89_, lean_object* v_eq_90_){
_start:
{
lean_inc(v_eq_90_);
return v_eq_90_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_eq_elim___boxed(lean_object* v_motive_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_eq_94_){
_start:
{
uint8_t v_t_boxed_95_; lean_object* v_res_96_; 
v_t_boxed_95_ = lean_unbox(v_t_92_);
v_res_96_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_eq_elim(v_motive_91_, v_t_boxed_95_, v_h_93_, v_eq_94_);
lean_dec(v_eq_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_le_elim___redArg(lean_object* v_le_97_){
_start:
{
lean_inc(v_le_97_);
return v_le_97_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_le_elim___redArg___boxed(lean_object* v_le_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_le_elim___redArg(v_le_98_);
lean_dec(v_le_98_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_le_elim(lean_object* v_motive_100_, uint8_t v_t_101_, lean_object* v_h_102_, lean_object* v_le_103_){
_start:
{
lean_inc(v_le_103_);
return v_le_103_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_le_elim___boxed(lean_object* v_motive_104_, lean_object* v_t_105_, lean_object* v_h_106_, lean_object* v_le_107_){
_start:
{
uint8_t v_t_boxed_108_; lean_object* v_res_109_; 
v_t_boxed_108_ = lean_unbox(v_t_105_);
v_res_109_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_le_elim(v_motive_104_, v_t_boxed_108_, v_h_106_, v_le_107_);
lean_dec(v_le_107_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_sub_elim___redArg(lean_object* v_sub_110_){
_start:
{
lean_inc(v_sub_110_);
return v_sub_110_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_sub_elim___redArg___boxed(lean_object* v_sub_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_sub_elim___redArg(v_sub_111_);
lean_dec(v_sub_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_sub_elim(lean_object* v_motive_113_, uint8_t v_t_114_, lean_object* v_h_115_, lean_object* v_sub_116_){
_start:
{
lean_inc(v_sub_116_);
return v_sub_116_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_sub_elim___boxed(lean_object* v_motive_117_, lean_object* v_t_118_, lean_object* v_h_119_, lean_object* v_sub_120_){
_start:
{
uint8_t v_t_boxed_121_; lean_object* v_res_122_; 
v_t_boxed_121_ = lean_unbox(v_t_118_);
v_res_122_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_sub_elim(v_motive_117_, v_t_boxed_121_, v_h_119_, v_sub_120_);
lean_dec(v_sub_120_);
return v_res_122_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ofNat(lean_object* v_n_123_){
_start:
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(2u);
v___x_125_ = lean_nat_dec_le(v_n_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(4u);
v___x_127_ = lean_nat_dec_le(v_n_123_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(5u);
v___x_129_ = lean_nat_dec_le(v_n_123_, v___x_128_);
if (v___x_129_ == 0)
{
uint8_t v___x_130_; 
v___x_130_ = 6;
return v___x_130_;
}
else
{
uint8_t v___x_131_; 
v___x_131_ = 5;
return v___x_131_;
}
}
else
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(3u);
v___x_133_ = lean_nat_dec_le(v_n_123_, v___x_132_);
if (v___x_133_ == 0)
{
uint8_t v___x_134_; 
v___x_134_ = 4;
return v___x_134_;
}
else
{
uint8_t v___x_135_; 
v___x_135_ = 3;
return v___x_135_;
}
}
}
else
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_nat_dec_le(v_n_123_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = lean_nat_dec_le(v_n_123_, v___x_138_);
if (v___x_139_ == 0)
{
uint8_t v___x_140_; 
v___x_140_ = 2;
return v___x_140_;
}
else
{
uint8_t v___x_141_; 
v___x_141_ = 1;
return v___x_141_;
}
}
else
{
uint8_t v___x_142_; 
v___x_142_ = 0;
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ofNat___boxed(lean_object* v_n_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ofNat(v_n_143_);
lean_dec(v_n_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Dsl_EmitPancake_instDecidableEqPOp(uint8_t v_x_146_, uint8_t v_y_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_148_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorIdx(v_x_146_);
v___x_149_ = lp_orb_x2dcompiler_Dsl_EmitPancake_POp_ctorIdx(v_y_147_);
v___x_150_ = lean_nat_dec_eq(v___x_148_, v___x_149_);
lean_dec(v___x_149_);
lean_dec(v___x_148_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instDecidableEqPOp___boxed(lean_object* v_x_151_, lean_object* v_y_152_){
_start:
{
uint8_t v_x_13__boxed_153_; uint8_t v_y_14__boxed_154_; uint8_t v_res_155_; lean_object* v_r_156_; 
v_x_13__boxed_153_ = lean_unbox(v_x_151_);
v_y_14__boxed_154_ = lean_unbox(v_y_152_);
v_res_155_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instDecidableEqPOp(v_x_13__boxed_153_, v_y_14__boxed_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(2u);
v___x_179_ = lean_nat_to_int(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_to_int(v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr(uint8_t v_x_182_, lean_object* v_prec_183_){
_start:
{
lean_object* v___y_185_; lean_object* v___y_192_; lean_object* v___y_199_; lean_object* v___y_206_; lean_object* v___y_213_; lean_object* v___y_220_; lean_object* v___y_227_; 
switch(v_x_182_)
{
case 0:
{
lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_233_ = lean_unsigned_to_nat(1024u);
v___x_234_ = lean_nat_dec_le(v___x_233_, v_prec_183_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; 
v___x_235_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_185_ = v___x_235_;
goto v___jp_184_;
}
else
{
lean_object* v___x_236_; 
v___x_236_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_185_ = v___x_236_;
goto v___jp_184_;
}
}
case 1:
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_unsigned_to_nat(1024u);
v___x_238_ = lean_nat_dec_le(v___x_237_, v_prec_183_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_192_ = v___x_239_;
goto v___jp_191_;
}
else
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_192_ = v___x_240_;
goto v___jp_191_;
}
}
case 2:
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = lean_unsigned_to_nat(1024u);
v___x_242_ = lean_nat_dec_le(v___x_241_, v_prec_183_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
v___x_243_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_199_ = v___x_243_;
goto v___jp_198_;
}
else
{
lean_object* v___x_244_; 
v___x_244_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_199_ = v___x_244_;
goto v___jp_198_;
}
}
case 3:
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = lean_unsigned_to_nat(1024u);
v___x_246_ = lean_nat_dec_le(v___x_245_, v_prec_183_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; 
v___x_247_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_206_ = v___x_247_;
goto v___jp_205_;
}
else
{
lean_object* v___x_248_; 
v___x_248_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_206_ = v___x_248_;
goto v___jp_205_;
}
}
case 4:
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_unsigned_to_nat(1024u);
v___x_250_ = lean_nat_dec_le(v___x_249_, v_prec_183_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
v___x_251_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_213_ = v___x_251_;
goto v___jp_212_;
}
else
{
lean_object* v___x_252_; 
v___x_252_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_213_ = v___x_252_;
goto v___jp_212_;
}
}
case 5:
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = lean_unsigned_to_nat(1024u);
v___x_254_ = lean_nat_dec_le(v___x_253_, v_prec_183_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
v___x_255_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_220_ = v___x_255_;
goto v___jp_219_;
}
else
{
lean_object* v___x_256_; 
v___x_256_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_220_ = v___x_256_;
goto v___jp_219_;
}
}
default: 
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_unsigned_to_nat(1024u);
v___x_258_ = lean_nat_dec_le(v___x_257_, v_prec_183_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
v___x_259_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_227_ = v___x_259_;
goto v___jp_226_;
}
else
{
lean_object* v___x_260_; 
v___x_260_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_227_ = v___x_260_;
goto v___jp_226_;
}
}
}
v___jp_184_:
{
lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_186_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__1));
lean_inc(v___y_185_);
v___x_187_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_187_, 0, v___y_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = 0;
v___x_189_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*1, v___x_188_);
v___x_190_ = l_Repr_addAppParen(v___x_189_, v_prec_183_);
return v___x_190_;
}
v___jp_191_:
{
lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_193_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__3));
lean_inc(v___y_192_);
v___x_194_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_194_, 0, v___y_192_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = 0;
v___x_196_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_196_, 0, v___x_194_);
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*1, v___x_195_);
v___x_197_ = l_Repr_addAppParen(v___x_196_, v_prec_183_);
return v___x_197_;
}
v___jp_198_:
{
lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_200_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__5));
lean_inc(v___y_199_);
v___x_201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_201_, 0, v___y_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = 0;
v___x_203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*1, v___x_202_);
v___x_204_ = l_Repr_addAppParen(v___x_203_, v_prec_183_);
return v___x_204_;
}
v___jp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_207_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__7));
lean_inc(v___y_206_);
v___x_208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_208_, 0, v___y_206_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = 0;
v___x_210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*1, v___x_209_);
v___x_211_ = l_Repr_addAppParen(v___x_210_, v_prec_183_);
return v___x_211_;
}
v___jp_212_:
{
lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_214_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__9));
lean_inc(v___y_213_);
v___x_215_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_215_, 0, v___y_213_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v___x_216_ = 0;
v___x_217_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set_uint8(v___x_217_, sizeof(void*)*1, v___x_216_);
v___x_218_ = l_Repr_addAppParen(v___x_217_, v_prec_183_);
return v___x_218_;
}
v___jp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_221_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__11));
lean_inc(v___y_220_);
v___x_222_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_222_, 0, v___y_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = 0;
v___x_224_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*1, v___x_223_);
v___x_225_ = l_Repr_addAppParen(v___x_224_, v_prec_183_);
return v___x_225_;
}
v___jp_226_:
{
lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_228_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__13));
lean_inc(v___y_227_);
v___x_229_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_229_, 0, v___y_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = 0;
v___x_231_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*1, v___x_230_);
v___x_232_ = l_Repr_addAppParen(v___x_231_, v_prec_183_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___boxed(lean_object* v_x_261_, lean_object* v_prec_262_){
_start:
{
uint8_t v_x_401__boxed_263_; lean_object* v_res_264_; 
v_x_401__boxed_263_ = lean_unbox(v_x_261_);
v_res_264_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr(v_x_401__boxed_263_, v_prec_262_);
lean_dec(v_prec_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorIdx(lean_object* v_x_267_){
_start:
{
switch(lean_obj_tag(v_x_267_))
{
case 0:
{
lean_object* v___x_268_; 
v___x_268_ = lean_unsigned_to_nat(0u);
return v___x_268_;
}
case 1:
{
lean_object* v___x_269_; 
v___x_269_ = lean_unsigned_to_nat(1u);
return v___x_269_;
}
case 2:
{
lean_object* v___x_270_; 
v___x_270_ = lean_unsigned_to_nat(2u);
return v___x_270_;
}
case 3:
{
lean_object* v___x_271_; 
v___x_271_ = lean_unsigned_to_nat(3u);
return v___x_271_;
}
case 4:
{
lean_object* v___x_272_; 
v___x_272_ = lean_unsigned_to_nat(4u);
return v___x_272_;
}
default: 
{
lean_object* v___x_273_; 
v___x_273_ = lean_unsigned_to_nat(5u);
return v___x_273_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorIdx___boxed(lean_object* v_x_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorIdx(v_x_274_);
lean_dec(v_x_274_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___redArg(lean_object* v_t_276_, lean_object* v_k_277_){
_start:
{
switch(lean_obj_tag(v_t_276_))
{
case 0:
{
return v_k_277_;
}
case 2:
{
lean_object* v_name_278_; lean_object* v___x_279_; 
v_name_278_ = lean_ctor_get(v_t_276_, 0);
lean_inc_ref(v_name_278_);
lean_dec_ref(v_t_276_);
v___x_279_ = lean_apply_1(v_k_277_, v_name_278_);
return v___x_279_;
}
case 3:
{
uint8_t v_op_280_; lean_object* v_l_281_; lean_object* v_r_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v_op_280_ = lean_ctor_get_uint8(v_t_276_, sizeof(void*)*2);
v_l_281_ = lean_ctor_get(v_t_276_, 0);
lean_inc(v_l_281_);
v_r_282_ = lean_ctor_get(v_t_276_, 1);
lean_inc(v_r_282_);
lean_dec_ref(v_t_276_);
v___x_283_ = lean_box(v_op_280_);
v___x_284_ = lean_apply_3(v_k_277_, v___x_283_, v_l_281_, v_r_282_);
return v___x_284_;
}
case 4:
{
lean_object* v_shape_285_; lean_object* v_addr_286_; lean_object* v___x_287_; 
v_shape_285_ = lean_ctor_get(v_t_276_, 0);
lean_inc(v_shape_285_);
v_addr_286_ = lean_ctor_get(v_t_276_, 1);
lean_inc(v_addr_286_);
lean_dec_ref(v_t_276_);
v___x_287_ = lean_apply_2(v_k_277_, v_shape_285_, v_addr_286_);
return v___x_287_;
}
default: 
{
lean_object* v_n_288_; lean_object* v___x_289_; 
v_n_288_ = lean_ctor_get(v_t_276_, 0);
lean_inc(v_n_288_);
lean_dec(v_t_276_);
v___x_289_ = lean_apply_1(v_k_277_, v_n_288_);
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim(lean_object* v_motive_290_, lean_object* v_ctorIdx_291_, lean_object* v_t_292_, lean_object* v_h_293_, lean_object* v_k_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___redArg(v_t_292_, v_k_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___boxed(lean_object* v_motive_296_, lean_object* v_ctorIdx_297_, lean_object* v_t_298_, lean_object* v_h_299_, lean_object* v_k_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim(v_motive_296_, v_ctorIdx_297_, v_t_298_, v_h_299_, v_k_300_);
lean_dec(v_ctorIdx_297_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_base_elim___redArg(lean_object* v_t_302_, lean_object* v_base_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___redArg(v_t_302_, v_base_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_base_elim(lean_object* v_motive_305_, lean_object* v_t_306_, lean_object* v_h_307_, lean_object* v_base_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___redArg(v_t_306_, v_base_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_const_elim___redArg(lean_object* v_t_310_, lean_object* v_const_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___redArg(v_t_310_, v_const_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_const_elim(lean_object* v_motive_313_, lean_object* v_t_314_, lean_object* v_h_315_, lean_object* v_const_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___redArg(v_t_314_, v_const_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_var_elim___redArg(lean_object* v_t_318_, lean_object* v_var_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___redArg(v_t_318_, v_var_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_var_elim(lean_object* v_motive_321_, lean_object* v_t_322_, lean_object* v_h_323_, lean_object* v_var_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___redArg(v_t_322_, v_var_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_binop_elim___redArg(lean_object* v_t_326_, lean_object* v_binop_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___redArg(v_t_326_, v_binop_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_binop_elim(lean_object* v_motive_329_, lean_object* v_t_330_, lean_object* v_h_331_, lean_object* v_binop_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___redArg(v_t_330_, v_binop_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_loadw_elim___redArg(lean_object* v_t_334_, lean_object* v_loadw_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___redArg(v_t_334_, v_loadw_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_loadw_elim(lean_object* v_motive_337_, lean_object* v_t_338_, lean_object* v_h_339_, lean_object* v_loadw_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___redArg(v_t_338_, v_loadw_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_loadb_elim___redArg(lean_object* v_t_342_, lean_object* v_loadb_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___redArg(v_t_342_, v_loadb_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_loadb_elim(lean_object* v_motive_345_, lean_object* v_t_346_, lean_object* v_h_347_, lean_object* v_loadb_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PExpr_ctorElim___redArg(v_t_346_, v_loadb_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(lean_object* v_x_383_, lean_object* v_prec_384_){
_start:
{
lean_object* v___y_386_; 
switch(lean_obj_tag(v_x_383_))
{
case 0:
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(1024u);
v___x_393_ = lean_nat_dec_le(v___x_392_, v_prec_384_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
v___x_394_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_386_ = v___x_394_;
goto v___jp_385_;
}
else
{
lean_object* v___x_395_; 
v___x_395_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_386_ = v___x_395_;
goto v___jp_385_;
}
}
case 1:
{
lean_object* v_n_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_416_; 
v_n_396_ = lean_ctor_get(v_x_383_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v_x_383_);
if (v_isSharedCheck_416_ == 0)
{
v___x_398_ = v_x_383_;
v_isShared_399_ = v_isSharedCheck_416_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_n_396_);
lean_dec(v_x_383_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_416_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___y_401_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = lean_unsigned_to_nat(1024u);
v___x_413_ = lean_nat_dec_le(v___x_412_, v_prec_384_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; 
v___x_414_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_401_ = v___x_414_;
goto v___jp_400_;
}
else
{
lean_object* v___x_415_; 
v___x_415_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_401_ = v___x_415_;
goto v___jp_400_;
}
v___jp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_402_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__4));
v___x_403_ = l_Nat_reprFast(v_n_396_);
if (v_isShared_399_ == 0)
{
lean_ctor_set_tag(v___x_398_, 3);
lean_ctor_set(v___x_398_, 0, v___x_403_);
v___x_405_ = v___x_398_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_411_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_402_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
lean_inc(v___y_401_);
v___x_407_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_407_, 0, v___y_401_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = 0;
v___x_409_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*1, v___x_408_);
v___x_410_ = l_Repr_addAppParen(v___x_409_, v_prec_384_);
return v___x_410_;
}
}
}
}
case 2:
{
lean_object* v_name_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_437_; 
v_name_417_ = lean_ctor_get(v_x_383_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_x_383_);
if (v_isSharedCheck_437_ == 0)
{
v___x_419_ = v_x_383_;
v_isShared_420_ = v_isSharedCheck_437_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_name_417_);
lean_dec(v_x_383_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_437_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___y_422_; lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = lean_unsigned_to_nat(1024u);
v___x_434_ = lean_nat_dec_le(v___x_433_, v_prec_384_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
v___x_435_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_422_ = v___x_435_;
goto v___jp_421_;
}
else
{
lean_object* v___x_436_; 
v___x_436_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_422_ = v___x_436_;
goto v___jp_421_;
}
v___jp_421_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_423_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__7));
v___x_424_ = l_String_quote(v_name_417_);
if (v_isShared_420_ == 0)
{
lean_ctor_set_tag(v___x_419_, 3);
lean_ctor_set(v___x_419_, 0, v___x_424_);
v___x_426_ = v___x_419_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_432_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_423_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
lean_inc(v___y_422_);
v___x_428_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_428_, 0, v___y_422_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = 0;
v___x_430_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*1, v___x_429_);
v___x_431_ = l_Repr_addAppParen(v___x_430_, v_prec_384_);
return v___x_431_;
}
}
}
}
case 3:
{
uint8_t v_op_438_; lean_object* v_l_439_; lean_object* v_r_440_; lean_object* v___x_441_; lean_object* v___y_443_; uint8_t v___x_458_; 
v_op_438_ = lean_ctor_get_uint8(v_x_383_, sizeof(void*)*2);
v_l_439_ = lean_ctor_get(v_x_383_, 0);
lean_inc(v_l_439_);
v_r_440_ = lean_ctor_get(v_x_383_, 1);
lean_inc(v_r_440_);
lean_dec_ref(v_x_383_);
v___x_441_ = lean_unsigned_to_nat(1024u);
v___x_458_ = lean_nat_dec_le(v___x_441_, v_prec_384_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
v___x_459_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_443_ = v___x_459_;
goto v___jp_442_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_443_ = v___x_460_;
goto v___jp_442_;
}
v___jp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_444_ = lean_box(1);
v___x_445_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__10));
v___x_446_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr(v_op_438_, v___x_441_);
v___x_447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v___x_444_);
v___x_449_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_l_439_, v___x_441_);
v___x_450_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v___x_444_);
v___x_452_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_r_440_, v___x_441_);
v___x_453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
lean_inc(v___y_443_);
v___x_454_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_454_, 0, v___y_443_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = 0;
v___x_456_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*1, v___x_455_);
v___x_457_ = l_Repr_addAppParen(v___x_456_, v_prec_384_);
return v___x_457_;
}
}
case 4:
{
lean_object* v_shape_461_; lean_object* v_addr_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_486_; 
v_shape_461_ = lean_ctor_get(v_x_383_, 0);
v_addr_462_ = lean_ctor_get(v_x_383_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_x_383_);
if (v_isSharedCheck_486_ == 0)
{
v___x_464_ = v_x_383_;
v_isShared_465_ = v_isSharedCheck_486_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_addr_462_);
lean_inc(v_shape_461_);
lean_dec(v_x_383_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_486_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___y_468_; uint8_t v___x_483_; 
v___x_466_ = lean_unsigned_to_nat(1024u);
v___x_483_ = lean_nat_dec_le(v___x_466_, v_prec_384_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_468_ = v___x_484_;
goto v___jp_467_;
}
else
{
lean_object* v___x_485_; 
v___x_485_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_468_ = v___x_485_;
goto v___jp_467_;
}
v___jp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_469_ = lean_box(1);
v___x_470_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__13));
v___x_471_ = l_Nat_reprFast(v_shape_461_);
v___x_472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
if (v_isShared_465_ == 0)
{
lean_ctor_set_tag(v___x_464_, 5);
lean_ctor_set(v___x_464_, 1, v___x_472_);
lean_ctor_set(v___x_464_, 0, v___x_470_);
v___x_474_ = v___x_464_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v___x_472_);
v___x_474_ = v_reuseFailAlloc_482_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v___x_469_);
v___x_476_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_addr_462_, v___x_466_);
v___x_477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
lean_inc(v___y_468_);
v___x_478_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_478_, 0, v___y_468_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = 0;
v___x_480_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*1, v___x_479_);
v___x_481_ = l_Repr_addAppParen(v___x_480_, v_prec_384_);
return v___x_481_;
}
}
}
}
default: 
{
lean_object* v_addr_487_; lean_object* v___x_488_; lean_object* v___y_490_; uint8_t v___x_498_; 
v_addr_487_ = lean_ctor_get(v_x_383_, 0);
lean_inc(v_addr_487_);
lean_dec_ref(v_x_383_);
v___x_488_ = lean_unsigned_to_nat(1024u);
v___x_498_ = lean_nat_dec_le(v___x_488_, v_prec_384_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
v___x_499_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_490_ = v___x_499_;
goto v___jp_489_;
}
else
{
lean_object* v___x_500_; 
v___x_500_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_490_ = v___x_500_;
goto v___jp_489_;
}
v___jp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_491_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__16));
v___x_492_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_addr_487_, v___x_488_);
v___x_493_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
lean_inc(v___y_490_);
v___x_494_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_494_, 0, v___y_490_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = 0;
v___x_496_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*1, v___x_495_);
v___x_497_ = l_Repr_addAppParen(v___x_496_, v_prec_384_);
return v___x_497_;
}
}
}
v___jp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_387_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___closed__1));
lean_inc(v___y_386_);
v___x_388_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_388_, 0, v___y_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = 0;
v___x_390_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*1, v___x_389_);
v___x_391_ = l_Repr_addAppParen(v___x_390_, v_prec_384_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr___boxed(lean_object* v_x_501_, lean_object* v_prec_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_x_501_, v_prec_502_);
lean_dec(v_prec_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorIdx(lean_object* v_x_506_){
_start:
{
switch(lean_obj_tag(v_x_506_))
{
case 0:
{
lean_object* v___x_507_; 
v___x_507_ = lean_unsigned_to_nat(0u);
return v___x_507_;
}
case 1:
{
lean_object* v___x_508_; 
v___x_508_ = lean_unsigned_to_nat(1u);
return v___x_508_;
}
case 2:
{
lean_object* v___x_509_; 
v___x_509_ = lean_unsigned_to_nat(2u);
return v___x_509_;
}
case 3:
{
lean_object* v___x_510_; 
v___x_510_ = lean_unsigned_to_nat(3u);
return v___x_510_;
}
case 4:
{
lean_object* v___x_511_; 
v___x_511_ = lean_unsigned_to_nat(4u);
return v___x_511_;
}
case 5:
{
lean_object* v___x_512_; 
v___x_512_ = lean_unsigned_to_nat(5u);
return v___x_512_;
}
case 6:
{
lean_object* v___x_513_; 
v___x_513_ = lean_unsigned_to_nat(6u);
return v___x_513_;
}
case 7:
{
lean_object* v___x_514_; 
v___x_514_ = lean_unsigned_to_nat(7u);
return v___x_514_;
}
default: 
{
lean_object* v___x_515_; 
v___x_515_ = lean_unsigned_to_nat(8u);
return v___x_515_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorIdx___boxed(lean_object* v_x_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorIdx(v_x_516_);
lean_dec_ref(v_x_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(lean_object* v_t_518_, lean_object* v_k_519_){
_start:
{
switch(lean_obj_tag(v_t_518_))
{
case 2:
{
lean_object* v_addr_520_; lean_object* v_val_521_; lean_object* v___x_522_; 
v_addr_520_ = lean_ctor_get(v_t_518_, 0);
lean_inc(v_addr_520_);
v_val_521_ = lean_ctor_get(v_t_518_, 1);
lean_inc(v_val_521_);
lean_dec_ref(v_t_518_);
v___x_522_ = lean_apply_2(v_k_519_, v_addr_520_, v_val_521_);
return v___x_522_;
}
case 3:
{
lean_object* v_addr_523_; lean_object* v_val_524_; lean_object* v___x_525_; 
v_addr_523_ = lean_ctor_get(v_t_518_, 0);
lean_inc(v_addr_523_);
v_val_524_ = lean_ctor_get(v_t_518_, 1);
lean_inc(v_val_524_);
lean_dec_ref(v_t_518_);
v___x_525_ = lean_apply_2(v_k_519_, v_addr_523_, v_val_524_);
return v___x_525_;
}
case 5:
{
lean_object* v_ret_526_; lean_object* v_fn_527_; lean_object* v_args_528_; lean_object* v___x_529_; 
v_ret_526_ = lean_ctor_get(v_t_518_, 0);
lean_inc_ref(v_ret_526_);
v_fn_527_ = lean_ctor_get(v_t_518_, 1);
lean_inc_ref(v_fn_527_);
v_args_528_ = lean_ctor_get(v_t_518_, 2);
lean_inc(v_args_528_);
lean_dec_ref(v_t_518_);
v___x_529_ = lean_apply_3(v_k_519_, v_ret_526_, v_fn_527_, v_args_528_);
return v___x_529_;
}
case 6:
{
lean_object* v_val_530_; lean_object* v___x_531_; 
v_val_530_ = lean_ctor_get(v_t_518_, 0);
lean_inc(v_val_530_);
lean_dec_ref(v_t_518_);
v___x_531_ = lean_apply_1(v_k_519_, v_val_530_);
return v___x_531_;
}
case 7:
{
lean_object* v_cond_532_; lean_object* v_thn_533_; lean_object* v_els_534_; lean_object* v___x_535_; 
v_cond_532_ = lean_ctor_get(v_t_518_, 0);
lean_inc(v_cond_532_);
v_thn_533_ = lean_ctor_get(v_t_518_, 1);
lean_inc(v_thn_533_);
v_els_534_ = lean_ctor_get(v_t_518_, 2);
lean_inc(v_els_534_);
lean_dec_ref(v_t_518_);
v___x_535_ = lean_apply_3(v_k_519_, v_cond_532_, v_thn_533_, v_els_534_);
return v___x_535_;
}
case 8:
{
lean_object* v_cond_536_; lean_object* v_body_537_; lean_object* v___x_538_; 
v_cond_536_ = lean_ctor_get(v_t_518_, 0);
lean_inc(v_cond_536_);
v_body_537_ = lean_ctor_get(v_t_518_, 1);
lean_inc(v_body_537_);
lean_dec_ref(v_t_518_);
v___x_538_ = lean_apply_2(v_k_519_, v_cond_536_, v_body_537_);
return v___x_538_;
}
default: 
{
lean_object* v_name_539_; lean_object* v_val_540_; lean_object* v___x_541_; 
v_name_539_ = lean_ctor_get(v_t_518_, 0);
lean_inc_ref(v_name_539_);
v_val_540_ = lean_ctor_get(v_t_518_, 1);
lean_inc(v_val_540_);
lean_dec_ref(v_t_518_);
v___x_541_ = lean_apply_2(v_k_519_, v_name_539_, v_val_540_);
return v___x_541_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim(lean_object* v_motive__1_542_, lean_object* v_ctorIdx_543_, lean_object* v_t_544_, lean_object* v_h_545_, lean_object* v_k_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_544_, v_k_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___boxed(lean_object* v_motive__1_548_, lean_object* v_ctorIdx_549_, lean_object* v_t_550_, lean_object* v_h_551_, lean_object* v_k_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim(v_motive__1_548_, v_ctorIdx_549_, v_t_550_, v_h_551_, v_k_552_);
lean_dec(v_ctorIdx_549_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_dec_elim___redArg(lean_object* v_t_554_, lean_object* v_dec_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_554_, v_dec_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_dec_elim(lean_object* v_motive__1_557_, lean_object* v_t_558_, lean_object* v_h_559_, lean_object* v_dec_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_558_, v_dec_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_assign_elim___redArg(lean_object* v_t_562_, lean_object* v_assign_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_562_, v_assign_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_assign_elim(lean_object* v_motive__1_565_, lean_object* v_t_566_, lean_object* v_h_567_, lean_object* v_assign_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_566_, v_assign_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_store_elim___redArg(lean_object* v_t_570_, lean_object* v_store_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_570_, v_store_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_store_elim(lean_object* v_motive__1_573_, lean_object* v_t_574_, lean_object* v_h_575_, lean_object* v_store_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_574_, v_store_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_storeb_elim___redArg(lean_object* v_t_578_, lean_object* v_storeb_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_578_, v_storeb_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_storeb_elim(lean_object* v_motive__1_581_, lean_object* v_t_582_, lean_object* v_h_583_, lean_object* v_storeb_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_582_, v_storeb_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ffi_elim___redArg(lean_object* v_t_586_, lean_object* v_ffi_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_586_, v_ffi_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ffi_elim(lean_object* v_motive__1_589_, lean_object* v_t_590_, lean_object* v_h_591_, lean_object* v_ffi_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_590_, v_ffi_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_call_elim___redArg(lean_object* v_t_594_, lean_object* v_call_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_594_, v_call_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_call_elim(lean_object* v_motive__1_597_, lean_object* v_t_598_, lean_object* v_h_599_, lean_object* v_call_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_598_, v_call_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ret_elim___redArg(lean_object* v_t_602_, lean_object* v_ret_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_602_, v_ret_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ret_elim(lean_object* v_motive__1_605_, lean_object* v_t_606_, lean_object* v_h_607_, lean_object* v_ret_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_606_, v_ret_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ite_elim___redArg(lean_object* v_t_610_, lean_object* v_ite_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_610_, v_ite_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ite_elim(lean_object* v_motive__1_613_, lean_object* v_t_614_, lean_object* v_h_615_, lean_object* v_ite_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_614_, v_ite_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_while_elim___redArg(lean_object* v_t_618_, lean_object* v_while_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_618_, v_while_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_while_elim(lean_object* v_motive__1_621_, lean_object* v_t_622_, lean_object* v_h_623_, lean_object* v_while_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_ctorElim___redArg(v_t_622_, v_while_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
if (lean_obj_tag(v_x_628_) == 0)
{
lean_dec(v_x_626_);
return v_x_627_;
}
else
{
lean_object* v_head_629_; lean_object* v_tail_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_641_; 
v_head_629_ = lean_ctor_get(v_x_628_, 0);
v_tail_630_ = lean_ctor_get(v_x_628_, 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v_x_628_);
if (v_isSharedCheck_641_ == 0)
{
v___x_632_ = v_x_628_;
v_isShared_633_ = v_isSharedCheck_641_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_tail_630_);
lean_inc(v_head_629_);
lean_dec(v_x_628_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_641_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
lean_inc(v_x_626_);
if (v_isShared_633_ == 0)
{
lean_ctor_set_tag(v___x_632_, 5);
lean_ctor_set(v___x_632_, 1, v_x_626_);
lean_ctor_set(v___x_632_, 0, v_x_627_);
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_x_627_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_x_626_);
v___x_635_ = v_reuseFailAlloc_640_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_head_629_, v___x_636_);
v___x_638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_635_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v_x_627_ = v___x_638_;
v_x_628_ = v_tail_630_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0_spec__0_spec__1(lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v_x_644_){
_start:
{
if (lean_obj_tag(v_x_644_) == 0)
{
lean_dec(v_x_642_);
return v_x_643_;
}
else
{
lean_object* v_head_645_; lean_object* v_tail_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_657_; 
v_head_645_ = lean_ctor_get(v_x_644_, 0);
v_tail_646_ = lean_ctor_get(v_x_644_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v_x_644_);
if (v_isSharedCheck_657_ == 0)
{
v___x_648_ = v_x_644_;
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_tail_646_);
lean_inc(v_head_645_);
lean_dec(v_x_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
lean_inc(v_x_642_);
if (v_isShared_649_ == 0)
{
lean_ctor_set_tag(v___x_648_, 5);
lean_ctor_set(v___x_648_, 1, v_x_642_);
lean_ctor_set(v___x_648_, 0, v_x_643_);
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_x_643_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_x_642_);
v___x_651_ = v_reuseFailAlloc_656_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_head_645_, v___x_652_);
v___x_654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_651_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = lp_orb_x2dcompiler_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0_spec__0_spec__1_spec__3(v_x_642_, v___x_654_, v_tail_646_);
return v___x_655_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0_spec__0___lam__0(lean_object* v___y_658_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v___y_658_, v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0_spec__0(lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_661_) == 0)
{
lean_object* v___x_663_; 
lean_dec(v_x_662_);
v___x_663_ = lean_box(0);
return v___x_663_;
}
else
{
lean_object* v_tail_664_; 
v_tail_664_ = lean_ctor_get(v_x_661_, 1);
if (lean_obj_tag(v_tail_664_) == 0)
{
lean_object* v_head_665_; lean_object* v___x_666_; 
lean_dec(v_x_662_);
v_head_665_ = lean_ctor_get(v_x_661_, 0);
lean_inc(v_head_665_);
lean_dec_ref(v_x_661_);
v___x_666_ = lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0_spec__0___lam__0(v_head_665_);
return v___x_666_;
}
else
{
lean_object* v_head_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
lean_inc(v_tail_664_);
v_head_667_ = lean_ctor_get(v_x_661_, 0);
lean_inc(v_head_667_);
lean_dec_ref(v_x_661_);
v___x_668_ = lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0_spec__0___lam__0(v_head_667_);
v___x_669_ = lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0_spec__0_spec__1(v_x_662_, v___x_668_, v_tail_664_);
return v___x_669_;
}
}
}
}
static lean_object* _init_lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__2));
v___x_682_ = lean_string_length(v___x_681_);
return v___x_682_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_obj_once(&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__7, &lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__7_once, _init_lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__7);
v___x_684_ = lean_nat_to_int(v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg(lean_object* v_a_689_){
_start:
{
if (lean_obj_tag(v_a_689_) == 0)
{
lean_object* v___x_690_; 
v___x_690_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__1));
return v___x_690_;
}
else
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; lean_object* v___x_700_; 
v___x_691_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__5));
v___x_692_ = lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0_spec__0(v_a_689_, v___x_691_);
v___x_693_ = lean_obj_once(&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8, &lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8_once, _init_lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8);
v___x_694_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__9));
v___x_695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_692_);
v___x_696_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__10));
v___x_697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_693_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = 0;
v___x_700_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*1, v___x_699_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
if (lean_obj_tag(v_x_751_) == 0)
{
lean_dec(v_x_749_);
return v_x_750_;
}
else
{
lean_object* v_head_752_; lean_object* v_tail_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_764_; 
v_head_752_ = lean_ctor_get(v_x_751_, 0);
v_tail_753_ = lean_ctor_get(v_x_751_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_764_ == 0)
{
v___x_755_ = v_x_751_;
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_tail_753_);
lean_inc(v_head_752_);
lean_dec(v_x_751_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
lean_inc(v_x_749_);
if (v_isShared_756_ == 0)
{
lean_ctor_set_tag(v___x_755_, 5);
lean_ctor_set(v___x_755_, 1, v_x_749_);
lean_ctor_set(v___x_755_, 0, v_x_750_);
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_x_750_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_x_749_);
v___x_758_ = v_reuseFailAlloc_763_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr(v_head_752_, v___x_759_);
v___x_761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_758_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v_x_750_ = v___x_761_;
v_x_751_ = v_tail_753_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1_spec__2_spec__4(lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
if (lean_obj_tag(v_x_767_) == 0)
{
lean_dec(v_x_765_);
return v_x_766_;
}
else
{
lean_object* v_head_768_; lean_object* v_tail_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_780_; 
v_head_768_ = lean_ctor_get(v_x_767_, 0);
v_tail_769_ = lean_ctor_get(v_x_767_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v_x_767_);
if (v_isSharedCheck_780_ == 0)
{
v___x_771_ = v_x_767_;
v_isShared_772_ = v_isSharedCheck_780_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_tail_769_);
lean_inc(v_head_768_);
lean_dec(v_x_767_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_780_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
lean_inc(v_x_765_);
if (v_isShared_772_ == 0)
{
lean_ctor_set_tag(v___x_771_, 5);
lean_ctor_set(v___x_771_, 1, v_x_765_);
lean_ctor_set(v___x_771_, 0, v_x_766_);
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_x_766_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_x_765_);
v___x_774_ = v_reuseFailAlloc_779_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr(v_head_768_, v___x_775_);
v___x_777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_774_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = lp_orb_x2dcompiler_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1_spec__2_spec__4_spec__6(v_x_765_, v___x_777_, v_tail_769_);
return v___x_778_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1_spec__2(lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
if (lean_obj_tag(v_x_781_) == 0)
{
lean_object* v___x_783_; 
lean_dec(v_x_782_);
v___x_783_ = lean_box(0);
return v___x_783_;
}
else
{
lean_object* v_tail_784_; 
v_tail_784_ = lean_ctor_get(v_x_781_, 1);
if (lean_obj_tag(v_tail_784_) == 0)
{
lean_object* v_head_785_; lean_object* v___x_786_; 
lean_dec(v_x_782_);
v_head_785_ = lean_ctor_get(v_x_781_, 0);
lean_inc(v_head_785_);
lean_dec_ref(v_x_781_);
v___x_786_ = lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1_spec__2___lam__0(v_head_785_);
return v___x_786_;
}
else
{
lean_object* v_head_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
lean_inc(v_tail_784_);
v_head_787_ = lean_ctor_get(v_x_781_, 0);
lean_inc(v_head_787_);
lean_dec_ref(v_x_781_);
v___x_788_ = lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1_spec__2___lam__0(v_head_787_);
v___x_789_ = lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1_spec__2_spec__4(v_x_782_, v___x_788_, v_tail_784_);
return v___x_789_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1___redArg(lean_object* v_a_790_){
_start:
{
if (lean_obj_tag(v_a_790_) == 0)
{
lean_object* v___x_791_; 
v___x_791_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__1));
return v___x_791_;
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; lean_object* v___x_801_; 
v___x_792_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__5));
v___x_793_ = lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1_spec__2(v_a_790_, v___x_792_);
v___x_794_ = lean_obj_once(&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8, &lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8_once, _init_lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8);
v___x_795_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__9));
v___x_796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v___x_793_);
v___x_797_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__10));
v___x_798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_794_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = 0;
v___x_801_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*1, v___x_800_);
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr(lean_object* v_x_808_, lean_object* v_prec_809_){
_start:
{
switch(lean_obj_tag(v_x_808_))
{
case 0:
{
lean_object* v_name_810_; lean_object* v_val_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_836_; 
v_name_810_ = lean_ctor_get(v_x_808_, 0);
v_val_811_ = lean_ctor_get(v_x_808_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_x_808_);
if (v_isSharedCheck_836_ == 0)
{
v___x_813_ = v_x_808_;
v_isShared_814_ = v_isSharedCheck_836_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_val_811_);
lean_inc(v_name_810_);
lean_dec(v_x_808_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_836_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___y_816_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = lean_unsigned_to_nat(1024u);
v___x_833_ = lean_nat_dec_le(v___x_832_, v_prec_809_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
v___x_834_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_816_ = v___x_834_;
goto v___jp_815_;
}
else
{
lean_object* v___x_835_; 
v___x_835_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_816_ = v___x_835_;
goto v___jp_815_;
}
v___jp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_817_ = lean_box(1);
v___x_818_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__2));
v___x_819_ = l_String_quote(v_name_810_);
v___x_820_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 5);
lean_ctor_set(v___x_813_, 1, v___x_820_);
lean_ctor_set(v___x_813_, 0, v___x_818_);
v___x_822_ = v___x_813_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_820_);
v___x_822_ = v_reuseFailAlloc_831_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_817_);
v___x_824_ = lean_unsigned_to_nat(1024u);
v___x_825_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_val_811_, v___x_824_);
v___x_826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_823_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
lean_inc(v___y_816_);
v___x_827_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_827_, 0, v___y_816_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = 0;
v___x_829_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*1, v___x_828_);
v___x_830_ = l_Repr_addAppParen(v___x_829_, v_prec_809_);
return v___x_830_;
}
}
}
}
case 1:
{
lean_object* v_name_837_; lean_object* v_val_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_863_; 
v_name_837_ = lean_ctor_get(v_x_808_, 0);
v_val_838_ = lean_ctor_get(v_x_808_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_x_808_);
if (v_isSharedCheck_863_ == 0)
{
v___x_840_ = v_x_808_;
v_isShared_841_ = v_isSharedCheck_863_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_val_838_);
lean_inc(v_name_837_);
lean_dec(v_x_808_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_863_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___y_843_; lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_859_ = lean_unsigned_to_nat(1024u);
v___x_860_ = lean_nat_dec_le(v___x_859_, v_prec_809_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
v___x_861_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_843_ = v___x_861_;
goto v___jp_842_;
}
else
{
lean_object* v___x_862_; 
v___x_862_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_843_ = v___x_862_;
goto v___jp_842_;
}
v___jp_842_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_844_ = lean_box(1);
v___x_845_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__5));
v___x_846_ = l_String_quote(v_name_837_);
v___x_847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
if (v_isShared_841_ == 0)
{
lean_ctor_set_tag(v___x_840_, 5);
lean_ctor_set(v___x_840_, 1, v___x_847_);
lean_ctor_set(v___x_840_, 0, v___x_845_);
v___x_849_ = v___x_840_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v___x_847_);
v___x_849_ = v_reuseFailAlloc_858_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v___x_844_);
v___x_851_ = lean_unsigned_to_nat(1024u);
v___x_852_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_val_838_, v___x_851_);
v___x_853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_850_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
lean_inc(v___y_843_);
v___x_854_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_854_, 0, v___y_843_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = 0;
v___x_856_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*1, v___x_855_);
v___x_857_ = l_Repr_addAppParen(v___x_856_, v_prec_809_);
return v___x_857_;
}
}
}
}
case 2:
{
lean_object* v_addr_864_; lean_object* v_val_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_889_; 
v_addr_864_ = lean_ctor_get(v_x_808_, 0);
v_val_865_ = lean_ctor_get(v_x_808_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v_x_808_);
if (v_isSharedCheck_889_ == 0)
{
v___x_867_ = v_x_808_;
v_isShared_868_ = v_isSharedCheck_889_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_val_865_);
lean_inc(v_addr_864_);
lean_dec(v_x_808_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_889_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___y_870_; lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_885_ = lean_unsigned_to_nat(1024u);
v___x_886_ = lean_nat_dec_le(v___x_885_, v_prec_809_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
v___x_887_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_870_ = v___x_887_;
goto v___jp_869_;
}
else
{
lean_object* v___x_888_; 
v___x_888_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_870_ = v___x_888_;
goto v___jp_869_;
}
v___jp_869_:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_871_ = lean_box(1);
v___x_872_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__8));
v___x_873_ = lean_unsigned_to_nat(1024u);
v___x_874_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_addr_864_, v___x_873_);
if (v_isShared_868_ == 0)
{
lean_ctor_set_tag(v___x_867_, 5);
lean_ctor_set(v___x_867_, 1, v___x_874_);
lean_ctor_set(v___x_867_, 0, v___x_872_);
v___x_876_ = v___x_867_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v___x_874_);
v___x_876_ = v_reuseFailAlloc_884_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v___x_871_);
v___x_878_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_val_865_, v___x_873_);
v___x_879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
lean_inc(v___y_870_);
v___x_880_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_880_, 0, v___y_870_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = 0;
v___x_882_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set_uint8(v___x_882_, sizeof(void*)*1, v___x_881_);
v___x_883_ = l_Repr_addAppParen(v___x_882_, v_prec_809_);
return v___x_883_;
}
}
}
}
case 3:
{
lean_object* v_addr_890_; lean_object* v_val_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_915_; 
v_addr_890_ = lean_ctor_get(v_x_808_, 0);
v_val_891_ = lean_ctor_get(v_x_808_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_x_808_);
if (v_isSharedCheck_915_ == 0)
{
v___x_893_ = v_x_808_;
v_isShared_894_ = v_isSharedCheck_915_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_val_891_);
lean_inc(v_addr_890_);
lean_dec(v_x_808_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_915_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___y_896_; lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_911_ = lean_unsigned_to_nat(1024u);
v___x_912_ = lean_nat_dec_le(v___x_911_, v_prec_809_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; 
v___x_913_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_896_ = v___x_913_;
goto v___jp_895_;
}
else
{
lean_object* v___x_914_; 
v___x_914_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_896_ = v___x_914_;
goto v___jp_895_;
}
v___jp_895_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_897_ = lean_box(1);
v___x_898_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__11));
v___x_899_ = lean_unsigned_to_nat(1024u);
v___x_900_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_addr_890_, v___x_899_);
if (v_isShared_894_ == 0)
{
lean_ctor_set_tag(v___x_893_, 5);
lean_ctor_set(v___x_893_, 1, v___x_900_);
lean_ctor_set(v___x_893_, 0, v___x_898_);
v___x_902_ = v___x_893_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v___x_900_);
v___x_902_ = v_reuseFailAlloc_910_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v___x_897_);
v___x_904_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_val_891_, v___x_899_);
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
lean_inc(v___y_896_);
v___x_906_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_906_, 0, v___y_896_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = 0;
v___x_908_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set_uint8(v___x_908_, sizeof(void*)*1, v___x_907_);
v___x_909_ = l_Repr_addAppParen(v___x_908_, v_prec_809_);
return v___x_909_;
}
}
}
}
case 4:
{
lean_object* v_name_916_; lean_object* v_args_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_941_; 
v_name_916_ = lean_ctor_get(v_x_808_, 0);
v_args_917_ = lean_ctor_get(v_x_808_, 1);
v_isSharedCheck_941_ = !lean_is_exclusive(v_x_808_);
if (v_isSharedCheck_941_ == 0)
{
v___x_919_ = v_x_808_;
v_isShared_920_ = v_isSharedCheck_941_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_args_917_);
lean_inc(v_name_916_);
lean_dec(v_x_808_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_941_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___y_922_; lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_937_ = lean_unsigned_to_nat(1024u);
v___x_938_ = lean_nat_dec_le(v___x_937_, v_prec_809_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; 
v___x_939_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_922_ = v___x_939_;
goto v___jp_921_;
}
else
{
lean_object* v___x_940_; 
v___x_940_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_922_ = v___x_940_;
goto v___jp_921_;
}
v___jp_921_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_923_ = lean_box(1);
v___x_924_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__14));
v___x_925_ = l_String_quote(v_name_916_);
v___x_926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
if (v_isShared_920_ == 0)
{
lean_ctor_set_tag(v___x_919_, 5);
lean_ctor_set(v___x_919_, 1, v___x_926_);
lean_ctor_set(v___x_919_, 0, v___x_924_);
v___x_928_ = v___x_919_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v___x_926_);
v___x_928_ = v_reuseFailAlloc_936_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_923_);
v___x_930_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg(v_args_917_);
v___x_931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
lean_inc(v___y_922_);
v___x_932_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_932_, 0, v___y_922_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = 0;
v___x_934_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*1, v___x_933_);
v___x_935_ = l_Repr_addAppParen(v___x_934_, v_prec_809_);
return v___x_935_;
}
}
}
}
case 5:
{
lean_object* v_ret_942_; lean_object* v_fn_943_; lean_object* v_args_944_; lean_object* v___y_946_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_ret_942_ = lean_ctor_get(v_x_808_, 0);
lean_inc_ref(v_ret_942_);
v_fn_943_ = lean_ctor_get(v_x_808_, 1);
lean_inc_ref(v_fn_943_);
v_args_944_ = lean_ctor_get(v_x_808_, 2);
lean_inc(v_args_944_);
lean_dec_ref(v_x_808_);
v___x_963_ = lean_unsigned_to_nat(1024u);
v___x_964_ = lean_nat_dec_le(v___x_963_, v_prec_809_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; 
v___x_965_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_946_ = v___x_965_;
goto v___jp_945_;
}
else
{
lean_object* v___x_966_; 
v___x_966_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_946_ = v___x_966_;
goto v___jp_945_;
}
v___jp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_947_ = lean_box(1);
v___x_948_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__17));
v___x_949_ = l_String_quote(v_ret_942_);
v___x_950_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
v___x_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_948_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set(v___x_952_, 1, v___x_947_);
v___x_953_ = l_String_quote(v_fn_943_);
v___x_954_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_952_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_947_);
v___x_957_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg(v_args_944_);
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
lean_inc(v___y_946_);
v___x_959_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_959_, 0, v___y_946_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = 0;
v___x_961_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*1, v___x_960_);
v___x_962_ = l_Repr_addAppParen(v___x_961_, v_prec_809_);
return v___x_962_;
}
}
case 6:
{
lean_object* v_val_967_; lean_object* v___y_969_; lean_object* v___x_978_; uint8_t v___x_979_; 
v_val_967_ = lean_ctor_get(v_x_808_, 0);
lean_inc(v_val_967_);
lean_dec_ref(v_x_808_);
v___x_978_ = lean_unsigned_to_nat(1024u);
v___x_979_ = lean_nat_dec_le(v___x_978_, v_prec_809_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
v___x_980_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_969_ = v___x_980_;
goto v___jp_968_;
}
else
{
lean_object* v___x_981_; 
v___x_981_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_969_ = v___x_981_;
goto v___jp_968_;
}
v___jp_968_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_970_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__20));
v___x_971_ = lean_unsigned_to_nat(1024u);
v___x_972_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_val_967_, v___x_971_);
v___x_973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_970_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
lean_inc(v___y_969_);
v___x_974_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_974_, 0, v___y_969_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = 0;
v___x_976_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*1, v___x_975_);
v___x_977_ = l_Repr_addAppParen(v___x_976_, v_prec_809_);
return v___x_977_;
}
}
case 7:
{
lean_object* v_cond_982_; lean_object* v_thn_983_; lean_object* v_els_984_; lean_object* v___y_986_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v_cond_982_ = lean_ctor_get(v_x_808_, 0);
lean_inc(v_cond_982_);
v_thn_983_ = lean_ctor_get(v_x_808_, 1);
lean_inc(v_thn_983_);
v_els_984_ = lean_ctor_get(v_x_808_, 2);
lean_inc(v_els_984_);
lean_dec_ref(v_x_808_);
v___x_1002_ = lean_unsigned_to_nat(1024u);
v___x_1003_ = lean_nat_dec_le(v___x_1002_, v_prec_809_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_986_ = v___x_1004_;
goto v___jp_985_;
}
else
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_986_ = v___x_1005_;
goto v___jp_985_;
}
v___jp_985_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_987_ = lean_box(1);
v___x_988_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__23));
v___x_989_ = lean_unsigned_to_nat(1024u);
v___x_990_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_cond_982_, v___x_989_);
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_988_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_987_);
v___x_993_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1___redArg(v_thn_983_);
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_987_);
v___x_996_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1___redArg(v_els_984_);
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
lean_inc(v___y_986_);
v___x_998_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_998_, 0, v___y_986_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = 0;
v___x_1000_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*1, v___x_999_);
v___x_1001_ = l_Repr_addAppParen(v___x_1000_, v_prec_809_);
return v___x_1001_;
}
}
default: 
{
lean_object* v_cond_1006_; lean_object* v_body_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1031_; 
v_cond_1006_ = lean_ctor_get(v_x_808_, 0);
v_body_1007_ = lean_ctor_get(v_x_808_, 1);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_x_808_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1009_ = v_x_808_;
v_isShared_1010_ = v_isSharedCheck_1031_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_body_1007_);
lean_inc(v_cond_1006_);
lean_dec(v_x_808_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1031_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___y_1012_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1027_ = lean_unsigned_to_nat(1024u);
v___x_1028_ = lean_nat_dec_le(v___x_1027_, v_prec_809_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__14);
v___y_1012_ = v___x_1029_;
goto v___jp_1011_;
}
else
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPOp_repr___closed__15);
v___y_1012_ = v___x_1030_;
goto v___jp_1011_;
}
v___jp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1013_ = lean_box(1);
v___x_1014_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___closed__26));
v___x_1015_ = lean_unsigned_to_nat(1024u);
v___x_1016_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPExpr_repr(v_cond_1006_, v___x_1015_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 5);
lean_ctor_set(v___x_1009_, 1, v___x_1016_);
lean_ctor_set(v___x_1009_, 0, v___x_1014_);
v___x_1018_ = v___x_1009_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v___x_1013_);
v___x_1020_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1___redArg(v_body_1007_);
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
lean_inc(v___y_1012_);
v___x_1022_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___y_1012_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = 0;
v___x_1024_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set_uint8(v___x_1024_, sizeof(void*)*1, v___x_1023_);
v___x_1025_ = l_Repr_addAppParen(v___x_1024_, v_prec_809_);
return v___x_1025_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1_spec__2___lam__0(lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr(v___y_1032_, v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr___boxed(lean_object* v_x_1035_, lean_object* v_prec_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPStmt_repr(v_x_1035_, v_prec_1036_);
lean_dec(v_prec_1036_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0(lean_object* v_a_1038_, lean_object* v_n_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg(v_a_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___boxed(lean_object* v_a_1041_, lean_object* v_n_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0(v_a_1041_, v_n_1042_);
lean_dec(v_n_1042_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1(lean_object* v_a_1044_, lean_object* v_n_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1___redArg(v_a_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1___boxed(lean_object* v_a_1047_, lean_object* v_n_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1(v_a_1047_, v_n_1048_);
lean_dec(v_n_1048_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__1___redArg(lean_object* v_a_1052_){
_start:
{
if (lean_obj_tag(v_a_1052_) == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__1));
return v___x_1053_;
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; 
v___x_1054_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__5));
v___x_1055_ = lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__1_spec__2(v_a_1052_, v___x_1054_);
v___x_1056_ = lean_obj_once(&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8, &lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8_once, _init_lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8);
v___x_1057_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__9));
v___x_1058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v___x_1055_);
v___x_1059_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__10));
v___x_1060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1056_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = 0;
v___x_1063_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set_uint8(v___x_1063_, sizeof(void*)*1, v___x_1062_);
return v___x_1063_;
}
}
}
static lean_object* _init_lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__0));
v___x_1067_ = lean_string_length(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_obj_once(&lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__2, &lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__2_once, _init_lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__2);
v___x_1069_ = lean_nat_to_int(v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg(lean_object* v_x_1074_){
_start:
{
lean_object* v_fst_1075_; lean_object* v_snd_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1100_; 
v_fst_1075_ = lean_ctor_get(v_x_1074_, 0);
v_snd_1076_ = lean_ctor_get(v_x_1074_, 1);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_x_1074_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1078_ = v_x_1074_;
v_isShared_1079_ = v_isSharedCheck_1100_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_snd_1076_);
lean_inc(v_fst_1075_);
lean_dec(v_x_1074_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1100_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1080_ = l_Nat_reprFast(v_fst_1075_);
v___x_1081_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
v___x_1082_ = lean_box(0);
if (v_isShared_1079_ == 0)
{
lean_ctor_set_tag(v___x_1078_, 1);
lean_ctor_set(v___x_1078_, 1, v___x_1082_);
lean_ctor_set(v___x_1078_, 0, v___x_1081_);
v___x_1084_ = v___x_1078_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; 
v___x_1085_ = l_String_quote(v_snd_1076_);
v___x_1086_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v___x_1084_);
v___x_1088_ = l_List_reverse___redArg(v___x_1087_);
v___x_1089_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__5));
v___x_1090_ = l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(v___x_1088_, v___x_1089_);
v___x_1091_ = lean_obj_once(&lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__3, &lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__3_once, _init_lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__3);
v___x_1092_ = ((lean_object*)(lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__4));
v___x_1093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v___x_1090_);
v___x_1094_ = ((lean_object*)(lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__5));
v___x_1095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1091_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = 0;
v___x_1098_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*1, v___x_1097_);
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_){
_start:
{
if (lean_obj_tag(v_x_1103_) == 0)
{
lean_dec(v_x_1101_);
return v_x_1102_;
}
else
{
lean_object* v_head_1104_; lean_object* v_tail_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1115_; 
v_head_1104_ = lean_ctor_get(v_x_1103_, 0);
v_tail_1105_ = lean_ctor_get(v_x_1103_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_x_1103_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1107_ = v_x_1103_;
v_isShared_1108_ = v_isSharedCheck_1115_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_tail_1105_);
lean_inc(v_head_1104_);
lean_dec(v_x_1103_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1115_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
lean_inc(v_x_1101_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set_tag(v___x_1107_, 5);
lean_ctor_set(v___x_1107_, 1, v_x_1101_);
lean_ctor_set(v___x_1107_, 0, v_x_1102_);
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_x_1102_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_x_1101_);
v___x_1110_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg(v_head_1104_);
v___x_1112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v_x_1102_ = v___x_1112_;
v_x_1103_ = v_tail_1105_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__1_spec__2(lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_){
_start:
{
if (lean_obj_tag(v_x_1118_) == 0)
{
lean_dec(v_x_1116_);
return v_x_1117_;
}
else
{
lean_object* v_head_1119_; lean_object* v_tail_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1130_; 
v_head_1119_ = lean_ctor_get(v_x_1118_, 0);
v_tail_1120_ = lean_ctor_get(v_x_1118_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_x_1118_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1122_ = v_x_1118_;
v_isShared_1123_ = v_isSharedCheck_1130_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_tail_1120_);
lean_inc(v_head_1119_);
lean_dec(v_x_1118_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1130_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
lean_inc(v_x_1116_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 5);
lean_ctor_set(v___x_1122_, 1, v_x_1116_);
lean_ctor_set(v___x_1122_, 0, v_x_1117_);
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_x_1117_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_x_1116_);
v___x_1125_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg(v_head_1119_);
v___x_1127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = lp_orb_x2dcompiler_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__1_spec__2_spec__4(v_x_1116_, v___x_1127_, v_tail_1120_);
return v___x_1128_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__1(lean_object* v_x_1131_, lean_object* v_x_1132_){
_start:
{
if (lean_obj_tag(v_x_1131_) == 0)
{
lean_object* v___x_1133_; 
lean_dec(v_x_1132_);
v___x_1133_ = lean_box(0);
return v___x_1133_;
}
else
{
lean_object* v_tail_1134_; 
v_tail_1134_ = lean_ctor_get(v_x_1131_, 1);
if (lean_obj_tag(v_tail_1134_) == 0)
{
lean_object* v_head_1135_; lean_object* v___x_1136_; 
lean_dec(v_x_1132_);
v_head_1135_ = lean_ctor_get(v_x_1131_, 0);
lean_inc(v_head_1135_);
lean_dec_ref(v_x_1131_);
v___x_1136_ = lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg(v_head_1135_);
return v___x_1136_;
}
else
{
lean_object* v_head_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_inc(v_tail_1134_);
v_head_1137_ = lean_ctor_get(v_x_1131_, 0);
lean_inc(v_head_1137_);
lean_dec_ref(v_x_1131_);
v___x_1138_ = lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg(v_head_1137_);
v___x_1139_ = lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__1_spec__2(v_x_1132_, v___x_1138_, v_tail_1134_);
return v___x_1139_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0___redArg(lean_object* v_a_1140_){
_start:
{
if (lean_obj_tag(v_a_1140_) == 0)
{
lean_object* v___x_1141_; 
v___x_1141_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__1));
return v___x_1141_;
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; lean_object* v___x_1151_; 
v___x_1142_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__5));
v___x_1143_ = lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__1(v_a_1140_, v___x_1142_);
v___x_1144_ = lean_obj_once(&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8, &lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8_once, _init_lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8);
v___x_1145_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__9));
v___x_1146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
lean_ctor_set(v___x_1146_, 1, v___x_1143_);
v___x_1147_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__10));
v___x_1148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1144_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = 0;
v___x_1151_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set_uint8(v___x_1151_, sizeof(void*)*1, v___x_1150_);
return v___x_1151_;
}
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_unsigned_to_nat(8u);
v___x_1166_ = lean_nat_to_int(v___x_1165_);
return v___x_1166_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_unsigned_to_nat(10u);
v___x_1171_ = lean_nat_to_int(v___x_1170_);
return v___x_1171_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = lean_unsigned_to_nat(12u);
v___x_1179_ = lean_nat_to_int(v___x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__0));
v___x_1182_ = lean_string_length(v___x_1181_);
return v___x_1182_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__17, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__17_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__17);
v___x_1184_ = lean_nat_to_int(v___x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg(lean_object* v_x_1189_){
_start:
{
lean_object* v_name_1190_; lean_object* v_params_1191_; lean_object* v_body_1192_; uint8_t v_exported_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_name_1190_ = lean_ctor_get(v_x_1189_, 0);
lean_inc_ref(v_name_1190_);
v_params_1191_ = lean_ctor_get(v_x_1189_, 1);
lean_inc(v_params_1191_);
v_body_1192_ = lean_ctor_get(v_x_1189_, 2);
lean_inc(v_body_1192_);
v_exported_1193_ = lean_ctor_get_uint8(v_x_1189_, sizeof(void*)*3);
lean_dec_ref(v_x_1189_);
v___x_1194_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__5));
v___x_1195_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__6));
v___x_1196_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__7, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__7_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__7);
v___x_1197_ = l_String_quote(v_name_1190_);
v___x_1198_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
v___x_1199_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1196_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = 0;
v___x_1201_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set_uint8(v___x_1201_, sizeof(void*)*1, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1195_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__4));
v___x_1204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1202_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = lean_box(1);
v___x_1206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1204_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__9));
v___x_1208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1194_);
v___x_1210_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__10, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__10_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__10);
v___x_1211_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0___redArg(v_params_1191_);
v___x_1212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set_uint8(v___x_1213_, sizeof(void*)*1, v___x_1200_);
v___x_1214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1209_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v___x_1203_);
v___x_1216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1205_);
v___x_1217_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__12));
v___x_1218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v___x_1194_);
v___x_1220_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__1___redArg(v_body_1192_);
v___x_1221_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1196_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set_uint8(v___x_1222_, sizeof(void*)*1, v___x_1200_);
v___x_1223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1219_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set(v___x_1224_, 1, v___x_1203_);
v___x_1225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v___x_1205_);
v___x_1226_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__14));
v___x_1227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1225_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
lean_ctor_set(v___x_1228_, 1, v___x_1194_);
v___x_1229_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__15);
v___x_1230_ = l_Bool_repr___redArg(v_exported_1193_);
v___x_1231_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set_uint8(v___x_1232_, sizeof(void*)*1, v___x_1200_);
v___x_1233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1228_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__18, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__18_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__18);
v___x_1235_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__19));
v___x_1236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v___x_1233_);
v___x_1237_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__20));
v___x_1238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1236_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1234_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set_uint8(v___x_1240_, sizeof(void*)*1, v___x_1200_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr(lean_object* v_x_1241_, lean_object* v_prec_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg(v_x_1241_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___boxed(lean_object* v_x_1244_, lean_object* v_prec_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr(v_x_1244_, v_prec_1245_);
lean_dec(v_prec_1245_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0(lean_object* v_a_1247_, lean_object* v_n_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0___redArg(v_a_1247_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0___boxed(lean_object* v_a_1250_, lean_object* v_n_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0(v_a_1250_, v_n_1251_);
lean_dec(v_n_1251_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__1(lean_object* v_a_1253_, lean_object* v_n_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__1___redArg(v_a_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__1___boxed(lean_object* v_a_1256_, lean_object* v_n_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__1(v_a_1256_, v_n_1257_);
lean_dec(v_n_1257_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0(lean_object* v_x_1259_, lean_object* v_x_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg(v_x_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___boxed(lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0(v_x_1262_, v_x_1263_);
lean_dec(v_x_1263_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_opSym(uint8_t v_x_1274_){
_start:
{
switch(v_x_1274_)
{
case 0:
{
lean_object* v___x_1275_; 
v___x_1275_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__0));
return v___x_1275_;
}
case 1:
{
lean_object* v___x_1276_; 
v___x_1276_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__1));
return v___x_1276_;
}
case 2:
{
lean_object* v___x_1277_; 
v___x_1277_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__2));
return v___x_1277_;
}
case 3:
{
lean_object* v___x_1278_; 
v___x_1278_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__3));
return v___x_1278_;
}
case 4:
{
lean_object* v___x_1279_; 
v___x_1279_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__4));
return v___x_1279_;
}
case 5:
{
lean_object* v___x_1280_; 
v___x_1280_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__5));
return v___x_1280_;
}
default: 
{
lean_object* v___x_1281_; 
v___x_1281_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___closed__6));
return v___x_1281_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_opSym___boxed(lean_object* v_x_1282_){
_start:
{
uint8_t v_x_67__boxed_1283_; lean_object* v_res_1284_; 
v_x_67__boxed_1283_ = lean_unbox(v_x_1282_);
v_res_1284_ = lp_orb_x2dcompiler_Dsl_EmitPancake_opSym(v_x_67__boxed_1283_);
return v_res_1284_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Dsl_EmitPancake_isAssoc(uint8_t v_x_1285_){
_start:
{
switch(v_x_1285_)
{
case 0:
{
uint8_t v___x_1286_; 
v___x_1286_ = 1;
return v___x_1286_;
}
case 1:
{
uint8_t v___x_1287_; 
v___x_1287_ = 1;
return v___x_1287_;
}
default: 
{
uint8_t v___x_1288_; 
v___x_1288_ = 0;
return v___x_1288_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_isAssoc___boxed(lean_object* v_x_1289_){
_start:
{
uint8_t v_x_43__boxed_1290_; uint8_t v_res_1291_; lean_object* v_r_1292_; 
v_x_43__boxed_1290_ = lean_unbox(v_x_1289_);
v_res_1291_ = lp_orb_x2dcompiler_Dsl_EmitPancake_isAssoc(v_x_43__boxed_1290_);
v_r_1292_ = lean_box(v_res_1291_);
return v_r_1292_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_wrapOperand(uint8_t v_parentOp_1293_, lean_object* v_child_1294_, lean_object* v_s_1295_){
_start:
{
uint8_t v___y_1297_; 
switch(lean_obj_tag(v_child_1294_))
{
case 3:
{
uint8_t v_op_1302_; uint8_t v___x_1303_; 
v_op_1302_ = lean_ctor_get_uint8(v_child_1294_, sizeof(void*)*2);
v___x_1303_ = lp_orb_x2dcompiler_Dsl_EmitPancake_isAssoc(v_parentOp_1293_);
if (v___x_1303_ == 0)
{
v___y_1297_ = v___x_1303_;
goto v___jp_1296_;
}
else
{
uint8_t v___x_1304_; 
v___x_1304_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instDecidableEqPOp(v_parentOp_1293_, v_op_1302_);
v___y_1297_ = v___x_1304_;
goto v___jp_1296_;
}
}
case 4:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1305_ = ((lean_object*)(lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__0));
v___x_1306_ = lean_string_append(v___x_1305_, v_s_1295_);
v___x_1307_ = ((lean_object*)(lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__1));
v___x_1308_ = lean_string_append(v___x_1306_, v___x_1307_);
return v___x_1308_;
}
case 5:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1309_ = ((lean_object*)(lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__0));
v___x_1310_ = lean_string_append(v___x_1309_, v_s_1295_);
v___x_1311_ = ((lean_object*)(lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__1));
v___x_1312_ = lean_string_append(v___x_1310_, v___x_1311_);
return v___x_1312_;
}
default: 
{
lean_inc_ref(v_s_1295_);
return v_s_1295_;
}
}
v___jp_1296_:
{
if (v___y_1297_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1298_ = ((lean_object*)(lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__0));
v___x_1299_ = lean_string_append(v___x_1298_, v_s_1295_);
v___x_1300_ = ((lean_object*)(lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__1));
v___x_1301_ = lean_string_append(v___x_1299_, v___x_1300_);
return v___x_1301_;
}
else
{
lean_inc_ref(v_s_1295_);
return v_s_1295_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_wrapOperand___boxed(lean_object* v_parentOp_1313_, lean_object* v_child_1314_, lean_object* v_s_1315_){
_start:
{
uint8_t v_parentOp_boxed_1316_; lean_object* v_res_1317_; 
v_parentOp_boxed_1316_ = lean_unbox(v_parentOp_1313_);
v_res_1317_ = lp_orb_x2dcompiler_Dsl_EmitPancake_wrapOperand(v_parentOp_boxed_1316_, v_child_1314_, v_s_1315_);
lean_dec_ref(v_s_1315_);
lean_dec(v_child_1314_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_wrapAtom(lean_object* v_child_1318_, lean_object* v_s_1319_){
_start:
{
if (lean_obj_tag(v_child_1318_) == 3)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1320_ = ((lean_object*)(lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__0));
v___x_1321_ = lean_string_append(v___x_1320_, v_s_1319_);
v___x_1322_ = ((lean_object*)(lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__1));
v___x_1323_ = lean_string_append(v___x_1321_, v___x_1322_);
return v___x_1323_;
}
else
{
lean_inc_ref(v_s_1319_);
return v_s_1319_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_wrapAtom___boxed(lean_object* v_child_1324_, lean_object* v_s_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = lp_orb_x2dcompiler_Dsl_EmitPancake_wrapAtom(v_child_1324_, v_s_1325_);
lean_dec_ref(v_s_1325_);
lean_dec(v_child_1324_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(lean_object* v_x_1331_){
_start:
{
switch(lean_obj_tag(v_x_1331_))
{
case 0:
{
lean_object* v___x_1332_; 
v___x_1332_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__0));
return v___x_1332_;
}
case 1:
{
lean_object* v_n_1333_; lean_object* v___x_1334_; 
v_n_1333_ = lean_ctor_get(v_x_1331_, 0);
lean_inc(v_n_1333_);
lean_dec_ref(v_x_1331_);
v___x_1334_ = l_Nat_reprFast(v_n_1333_);
return v___x_1334_;
}
case 2:
{
lean_object* v_name_1335_; 
v_name_1335_ = lean_ctor_get(v_x_1331_, 0);
lean_inc_ref(v_name_1335_);
lean_dec_ref(v_x_1331_);
return v_name_1335_;
}
case 3:
{
uint8_t v_op_1336_; lean_object* v_l_1337_; lean_object* v_r_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_op_1336_ = lean_ctor_get_uint8(v_x_1331_, sizeof(void*)*2);
v_l_1337_ = lean_ctor_get(v_x_1331_, 0);
lean_inc_n(v_l_1337_, 2);
v_r_1338_ = lean_ctor_get(v_x_1331_, 1);
lean_inc_n(v_r_1338_, 2);
lean_dec_ref(v_x_1331_);
v___x_1339_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(v_l_1337_);
v___x_1340_ = lp_orb_x2dcompiler_Dsl_EmitPancake_wrapOperand(v_op_1336_, v_l_1337_, v___x_1339_);
lean_dec_ref(v___x_1339_);
lean_dec(v_l_1337_);
v___x_1341_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__1));
v___x_1342_ = lean_string_append(v___x_1340_, v___x_1341_);
v___x_1343_ = lp_orb_x2dcompiler_Dsl_EmitPancake_opSym(v_op_1336_);
v___x_1344_ = lean_string_append(v___x_1342_, v___x_1343_);
lean_dec_ref(v___x_1343_);
v___x_1345_ = lean_string_append(v___x_1344_, v___x_1341_);
v___x_1346_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(v_r_1338_);
v___x_1347_ = lp_orb_x2dcompiler_Dsl_EmitPancake_wrapOperand(v_op_1336_, v_r_1338_, v___x_1346_);
lean_dec_ref(v___x_1346_);
lean_dec(v_r_1338_);
v___x_1348_ = lean_string_append(v___x_1345_, v___x_1347_);
lean_dec_ref(v___x_1347_);
return v___x_1348_;
}
case 4:
{
lean_object* v_shape_1349_; lean_object* v_addr_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v_shape_1349_ = lean_ctor_get(v_x_1331_, 0);
lean_inc(v_shape_1349_);
v_addr_1350_ = lean_ctor_get(v_x_1331_, 1);
lean_inc_n(v_addr_1350_, 2);
lean_dec_ref(v_x_1331_);
v___x_1351_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__2));
v___x_1352_ = l_Nat_reprFast(v_shape_1349_);
v___x_1353_ = lean_string_append(v___x_1351_, v___x_1352_);
lean_dec_ref(v___x_1352_);
v___x_1354_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__1));
v___x_1355_ = lean_string_append(v___x_1353_, v___x_1354_);
v___x_1356_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(v_addr_1350_);
v___x_1357_ = lp_orb_x2dcompiler_Dsl_EmitPancake_wrapAtom(v_addr_1350_, v___x_1356_);
lean_dec_ref(v___x_1356_);
lean_dec(v_addr_1350_);
v___x_1358_ = lean_string_append(v___x_1355_, v___x_1357_);
lean_dec_ref(v___x_1357_);
return v___x_1358_;
}
default: 
{
lean_object* v_addr_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_addr_1359_ = lean_ctor_get(v_x_1331_, 0);
lean_inc_n(v_addr_1359_, 2);
lean_dec_ref(v_x_1331_);
v___x_1360_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__3));
v___x_1361_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(v_addr_1359_);
v___x_1362_ = lp_orb_x2dcompiler_Dsl_EmitPancake_wrapAtom(v_addr_1359_, v___x_1361_);
lean_dec_ref(v___x_1361_);
lean_dec(v_addr_1359_);
v___x_1363_ = lean_string_append(v___x_1360_, v___x_1362_);
lean_dec_ref(v___x_1362_);
return v___x_1363_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_ppStmt_spec__0(lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
if (lean_obj_tag(v_a_1364_) == 0)
{
lean_object* v___x_1366_; 
v___x_1366_ = l_List_reverse___redArg(v_a_1365_);
return v___x_1366_;
}
else
{
lean_object* v_head_1367_; lean_object* v_tail_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1377_; 
v_head_1367_ = lean_ctor_get(v_a_1364_, 0);
v_tail_1368_ = lean_ctor_get(v_a_1364_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_a_1364_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1370_ = v_a_1364_;
v_isShared_1371_ = v_isSharedCheck_1377_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_tail_1368_);
lean_inc(v_head_1367_);
lean_dec(v_a_1364_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1377_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1372_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(v_head_1367_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v_a_1365_);
lean_ctor_set(v___x_1370_, 0, v___x_1372_);
v___x_1374_ = v___x_1370_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_a_1365_);
v___x_1374_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
v_a_1364_ = v_tail_1368_;
v_a_1365_ = v___x_1374_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt(lean_object* v_ind_1393_, lean_object* v_x_1394_){
_start:
{
switch(lean_obj_tag(v_x_1394_))
{
case 0:
{
lean_object* v_name_1395_; lean_object* v_val_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1413_; 
v_name_1395_ = lean_ctor_get(v_x_1394_, 0);
v_val_1396_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1398_ = v_x_1394_;
v_isShared_1399_ = v_isSharedCheck_1413_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_val_1396_);
lean_inc(v_name_1395_);
lean_dec(v_x_1394_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1413_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1400_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__0));
v___x_1401_ = lean_string_append(v_ind_1393_, v___x_1400_);
v___x_1402_ = lean_string_append(v___x_1401_, v_name_1395_);
lean_dec_ref(v_name_1395_);
v___x_1403_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__1));
v___x_1404_ = lean_string_append(v___x_1402_, v___x_1403_);
v___x_1405_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(v_val_1396_);
v___x_1406_ = lean_string_append(v___x_1404_, v___x_1405_);
lean_dec_ref(v___x_1405_);
v___x_1407_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__2));
v___x_1408_ = lean_string_append(v___x_1406_, v___x_1407_);
v___x_1409_ = lean_box(0);
if (v_isShared_1399_ == 0)
{
lean_ctor_set_tag(v___x_1398_, 1);
lean_ctor_set(v___x_1398_, 1, v___x_1409_);
lean_ctor_set(v___x_1398_, 0, v___x_1408_);
v___x_1411_ = v___x_1398_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
case 1:
{
lean_object* v_name_1414_; lean_object* v_val_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1430_; 
v_name_1414_ = lean_ctor_get(v_x_1394_, 0);
v_val_1415_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1417_ = v_x_1394_;
v_isShared_1418_ = v_isSharedCheck_1430_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_val_1415_);
lean_inc(v_name_1414_);
lean_dec(v_x_1394_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1430_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1419_ = lean_string_append(v_ind_1393_, v_name_1414_);
lean_dec_ref(v_name_1414_);
v___x_1420_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__1));
v___x_1421_ = lean_string_append(v___x_1419_, v___x_1420_);
v___x_1422_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(v_val_1415_);
v___x_1423_ = lean_string_append(v___x_1421_, v___x_1422_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__2));
v___x_1425_ = lean_string_append(v___x_1423_, v___x_1424_);
v___x_1426_ = lean_box(0);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 1, v___x_1426_);
lean_ctor_set(v___x_1417_, 0, v___x_1425_);
v___x_1428_ = v___x_1417_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
case 2:
{
lean_object* v_addr_1431_; lean_object* v_val_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1450_; 
v_addr_1431_ = lean_ctor_get(v_x_1394_, 0);
v_val_1432_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1434_ = v_x_1394_;
v_isShared_1435_ = v_isSharedCheck_1450_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_val_1432_);
lean_inc(v_addr_1431_);
lean_dec(v_x_1394_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1450_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1436_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__3));
v___x_1437_ = lean_string_append(v_ind_1393_, v___x_1436_);
v___x_1438_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(v_addr_1431_);
v___x_1439_ = lean_string_append(v___x_1437_, v___x_1438_);
lean_dec_ref(v___x_1438_);
v___x_1440_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__4));
v___x_1441_ = lean_string_append(v___x_1439_, v___x_1440_);
v___x_1442_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(v_val_1432_);
v___x_1443_ = lean_string_append(v___x_1441_, v___x_1442_);
lean_dec_ref(v___x_1442_);
v___x_1444_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__2));
v___x_1445_ = lean_string_append(v___x_1443_, v___x_1444_);
v___x_1446_ = lean_box(0);
if (v_isShared_1435_ == 0)
{
lean_ctor_set_tag(v___x_1434_, 1);
lean_ctor_set(v___x_1434_, 1, v___x_1446_);
lean_ctor_set(v___x_1434_, 0, v___x_1445_);
v___x_1448_ = v___x_1434_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v___x_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
case 3:
{
lean_object* v_addr_1451_; lean_object* v_val_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1470_; 
v_addr_1451_ = lean_ctor_get(v_x_1394_, 0);
v_val_1452_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1454_ = v_x_1394_;
v_isShared_1455_ = v_isSharedCheck_1470_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_val_1452_);
lean_inc(v_addr_1451_);
lean_dec(v_x_1394_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1470_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1456_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__5));
v___x_1457_ = lean_string_append(v_ind_1393_, v___x_1456_);
v___x_1458_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(v_addr_1451_);
v___x_1459_ = lean_string_append(v___x_1457_, v___x_1458_);
lean_dec_ref(v___x_1458_);
v___x_1460_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__4));
v___x_1461_ = lean_string_append(v___x_1459_, v___x_1460_);
v___x_1462_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(v_val_1452_);
v___x_1463_ = lean_string_append(v___x_1461_, v___x_1462_);
lean_dec_ref(v___x_1462_);
v___x_1464_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__2));
v___x_1465_ = lean_string_append(v___x_1463_, v___x_1464_);
v___x_1466_ = lean_box(0);
if (v_isShared_1455_ == 0)
{
lean_ctor_set_tag(v___x_1454_, 1);
lean_ctor_set(v___x_1454_, 1, v___x_1466_);
lean_ctor_set(v___x_1454_, 0, v___x_1465_);
v___x_1468_ = v___x_1454_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
case 4:
{
lean_object* v_name_1471_; lean_object* v_args_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1491_; 
v_name_1471_ = lean_ctor_get(v_x_1394_, 0);
v_args_1472_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1474_ = v_x_1394_;
v_isShared_1475_ = v_isSharedCheck_1491_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_args_1472_);
lean_inc(v_name_1471_);
lean_dec(v_x_1394_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1491_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1476_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__6));
v___x_1477_ = lean_string_append(v_ind_1393_, v___x_1476_);
v___x_1478_ = lean_string_append(v___x_1477_, v_name_1471_);
lean_dec_ref(v_name_1471_);
v___x_1479_ = ((lean_object*)(lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__0));
v___x_1480_ = lean_string_append(v___x_1478_, v___x_1479_);
v___x_1481_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__4));
v___x_1482_ = lean_box(0);
v___x_1483_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_ppStmt_spec__0(v_args_1472_, v___x_1482_);
v___x_1484_ = l_String_intercalate(v___x_1481_, v___x_1483_);
v___x_1485_ = lean_string_append(v___x_1480_, v___x_1484_);
lean_dec_ref(v___x_1484_);
v___x_1486_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__7));
v___x_1487_ = lean_string_append(v___x_1485_, v___x_1486_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set_tag(v___x_1474_, 1);
lean_ctor_set(v___x_1474_, 1, v___x_1482_);
lean_ctor_set(v___x_1474_, 0, v___x_1487_);
v___x_1489_ = v___x_1474_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___x_1482_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
case 5:
{
lean_object* v_ret_1492_; lean_object* v_fn_1493_; lean_object* v_args_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v_ret_1492_ = lean_ctor_get(v_x_1394_, 0);
lean_inc_ref(v_ret_1492_);
v_fn_1493_ = lean_ctor_get(v_x_1394_, 1);
lean_inc_ref(v_fn_1493_);
v_args_1494_ = lean_ctor_get(v_x_1394_, 2);
lean_inc(v_args_1494_);
lean_dec_ref(v_x_1394_);
v___x_1495_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__0));
v___x_1496_ = lean_string_append(v_ind_1393_, v___x_1495_);
v___x_1497_ = lean_string_append(v___x_1496_, v_ret_1492_);
lean_dec_ref(v_ret_1492_);
v___x_1498_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__1));
v___x_1499_ = lean_string_append(v___x_1497_, v___x_1498_);
v___x_1500_ = lean_string_append(v___x_1499_, v_fn_1493_);
lean_dec_ref(v_fn_1493_);
v___x_1501_ = ((lean_object*)(lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__0));
v___x_1502_ = lean_string_append(v___x_1500_, v___x_1501_);
v___x_1503_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__4));
v___x_1504_ = lean_box(0);
v___x_1505_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_ppStmt_spec__0(v_args_1494_, v___x_1504_);
v___x_1506_ = l_String_intercalate(v___x_1503_, v___x_1505_);
v___x_1507_ = lean_string_append(v___x_1502_, v___x_1506_);
lean_dec_ref(v___x_1506_);
v___x_1508_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__7));
v___x_1509_ = lean_string_append(v___x_1507_, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v___x_1504_);
return v___x_1510_;
}
case 6:
{
lean_object* v_val_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_val_1511_ = lean_ctor_get(v_x_1394_, 0);
lean_inc(v_val_1511_);
lean_dec_ref(v_x_1394_);
v___x_1512_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__8));
v___x_1513_ = lean_string_append(v_ind_1393_, v___x_1512_);
v___x_1514_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(v_val_1511_);
v___x_1515_ = lean_string_append(v___x_1513_, v___x_1514_);
lean_dec_ref(v___x_1514_);
v___x_1516_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__2));
v___x_1517_ = lean_string_append(v___x_1515_, v___x_1516_);
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
return v___x_1519_;
}
case 7:
{
lean_object* v_cond_1520_; lean_object* v_thn_1521_; lean_object* v_els_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_cond_1520_ = lean_ctor_get(v_x_1394_, 0);
lean_inc(v_cond_1520_);
v_thn_1521_ = lean_ctor_get(v_x_1394_, 1);
lean_inc(v_thn_1521_);
v_els_1522_ = lean_ctor_get(v_x_1394_, 2);
lean_inc(v_els_1522_);
lean_dec_ref(v_x_1394_);
v___x_1523_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__9));
lean_inc_ref_n(v_ind_1393_, 3);
v___x_1524_ = lean_string_append(v_ind_1393_, v___x_1523_);
v___x_1525_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(v_cond_1520_);
v___x_1526_ = lean_string_append(v___x_1524_, v___x_1525_);
lean_dec_ref(v___x_1525_);
v___x_1527_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__10));
v___x_1528_ = lean_string_append(v___x_1526_, v___x_1527_);
v___x_1529_ = lean_box(0);
v___x_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__11));
v___x_1532_ = lean_string_append(v_ind_1393_, v___x_1531_);
lean_inc_ref(v___x_1532_);
v___x_1533_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmts(v___x_1532_, v_thn_1521_);
v___x_1534_ = l_List_appendTR___redArg(v___x_1530_, v___x_1533_);
v___x_1535_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__12));
v___x_1536_ = lean_string_append(v_ind_1393_, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v___x_1529_);
v___x_1538_ = l_List_appendTR___redArg(v___x_1534_, v___x_1537_);
v___x_1539_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmts(v___x_1532_, v_els_1522_);
v___x_1540_ = l_List_appendTR___redArg(v___x_1538_, v___x_1539_);
v___x_1541_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__13));
v___x_1542_ = lean_string_append(v_ind_1393_, v___x_1541_);
v___x_1543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v___x_1529_);
v___x_1544_ = l_List_appendTR___redArg(v___x_1540_, v___x_1543_);
return v___x_1544_;
}
default: 
{
lean_object* v_cond_1545_; lean_object* v_body_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1568_; 
v_cond_1545_ = lean_ctor_get(v_x_1394_, 0);
v_body_1546_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1548_ = v_x_1394_;
v_isShared_1549_ = v_isSharedCheck_1568_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_body_1546_);
lean_inc(v_cond_1545_);
lean_dec(v_x_1394_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1568_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1550_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__14));
lean_inc_ref(v_ind_1393_);
v___x_1551_ = lean_string_append(v_ind_1393_, v___x_1550_);
v___x_1552_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr(v_cond_1545_);
v___x_1553_ = lean_string_append(v___x_1551_, v___x_1552_);
lean_dec_ref(v___x_1552_);
v___x_1554_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__10));
v___x_1555_ = lean_string_append(v___x_1553_, v___x_1554_);
v___x_1556_ = lean_box(0);
if (v_isShared_1549_ == 0)
{
lean_ctor_set_tag(v___x_1548_, 1);
lean_ctor_set(v___x_1548_, 1, v___x_1556_);
lean_ctor_set(v___x_1548_, 0, v___x_1555_);
v___x_1558_ = v___x_1548_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1559_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__11));
lean_inc_ref(v_ind_1393_);
v___x_1560_ = lean_string_append(v_ind_1393_, v___x_1559_);
v___x_1561_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmts(v___x_1560_, v_body_1546_);
v___x_1562_ = l_List_appendTR___redArg(v___x_1558_, v___x_1561_);
v___x_1563_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__13));
v___x_1564_ = lean_string_append(v_ind_1393_, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_ctor_set(v___x_1565_, 1, v___x_1556_);
v___x_1566_ = l_List_appendTR___redArg(v___x_1562_, v___x_1565_);
return v___x_1566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmts(lean_object* v_ind_1569_, lean_object* v_x_1570_){
_start:
{
if (lean_obj_tag(v_x_1570_) == 0)
{
lean_object* v___x_1571_; 
lean_dec_ref(v_ind_1569_);
v___x_1571_ = lean_box(0);
return v___x_1571_;
}
else
{
lean_object* v_head_1572_; lean_object* v_tail_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_head_1572_ = lean_ctor_get(v_x_1570_, 0);
lean_inc(v_head_1572_);
v_tail_1573_ = lean_ctor_get(v_x_1570_, 1);
lean_inc(v_tail_1573_);
lean_dec_ref(v_x_1570_);
lean_inc_ref(v_ind_1569_);
v___x_1574_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt(v_ind_1569_, v_head_1572_);
v___x_1575_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmts(v_ind_1569_, v_tail_1573_);
v___x_1576_ = l_List_appendTR___redArg(v___x_1574_, v___x_1575_);
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_ppFun_spec__0(lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
if (lean_obj_tag(v_a_1577_) == 0)
{
lean_object* v___x_1579_; 
v___x_1579_ = l_List_reverse___redArg(v_a_1578_);
return v___x_1579_;
}
else
{
lean_object* v_head_1580_; lean_object* v_tail_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1595_; 
v_head_1580_ = lean_ctor_get(v_a_1577_, 0);
v_tail_1581_ = lean_ctor_get(v_a_1577_, 1);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_a_1577_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1583_ = v_a_1577_;
v_isShared_1584_ = v_isSharedCheck_1595_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_tail_1581_);
lean_inc(v_head_1580_);
lean_dec(v_a_1577_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1595_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v_fst_1585_; lean_object* v_snd_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v_fst_1585_ = lean_ctor_get(v_head_1580_, 0);
lean_inc(v_fst_1585_);
v_snd_1586_ = lean_ctor_get(v_head_1580_, 1);
lean_inc(v_snd_1586_);
lean_dec(v_head_1580_);
v___x_1587_ = l_Nat_reprFast(v_fst_1585_);
v___x_1588_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppExpr___closed__1));
v___x_1589_ = lean_string_append(v___x_1587_, v___x_1588_);
v___x_1590_ = lean_string_append(v___x_1589_, v_snd_1586_);
lean_dec(v_snd_1586_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 1, v_a_1578_);
lean_ctor_set(v___x_1583_, 0, v___x_1590_);
v___x_1592_ = v___x_1583_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_a_1578_);
v___x_1592_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
v_a_1577_ = v_tail_1581_;
v_a_1578_ = v___x_1592_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun(lean_object* v_f_1603_){
_start:
{
lean_object* v_name_1604_; lean_object* v_params_1605_; lean_object* v_body_1606_; uint8_t v_exported_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v_ps_1611_; lean_object* v___y_1613_; 
v_name_1604_ = lean_ctor_get(v_f_1603_, 0);
lean_inc_ref(v_name_1604_);
v_params_1605_ = lean_ctor_get(v_f_1603_, 1);
lean_inc(v_params_1605_);
v_body_1606_ = lean_ctor_get(v_f_1603_, 2);
lean_inc(v_body_1606_);
v_exported_1607_ = lean_ctor_get_uint8(v_f_1603_, sizeof(void*)*3);
lean_dec_ref(v_f_1603_);
v___x_1608_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__4));
v___x_1609_ = lean_box(0);
v___x_1610_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_ppFun_spec__0(v_params_1605_, v___x_1609_);
v_ps_1611_ = l_String_intercalate(v___x_1608_, v___x_1610_);
if (v_exported_1607_ == 0)
{
lean_object* v___x_1628_; 
v___x_1628_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__3));
v___y_1613_ = v___x_1628_;
goto v___jp_1612_;
}
else
{
lean_object* v___x_1629_; 
v___x_1629_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__4));
v___y_1613_ = v___x_1629_;
goto v___jp_1612_;
}
v___jp_1612_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v_header_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_inc_ref(v___y_1613_);
v___x_1614_ = lean_string_append(v___y_1613_, v_name_1604_);
lean_dec_ref(v_name_1604_);
v___x_1615_ = ((lean_object*)(lp_orb_x2dcompiler_Prod_repr___at___00List_repr___at___00Dsl_EmitPancake_instReprPFun_repr_spec__0_spec__0___redArg___closed__0));
v___x_1616_ = lean_string_append(v___x_1614_, v___x_1615_);
v___x_1617_ = lean_string_append(v___x_1616_, v_ps_1611_);
lean_dec_ref(v_ps_1611_);
v___x_1618_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__0));
v_header_1619_ = lean_string_append(v___x_1617_, v___x_1618_);
v___x_1620_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__1));
v___x_1621_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmt___closed__11));
v___x_1622_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppStmts(v___x_1621_, v_body_1606_);
v___x_1623_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__2));
v___x_1624_ = l_List_appendTR___redArg(v___x_1622_, v___x_1623_);
v___x_1625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1625_, 0, v_header_1619_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = l_String_intercalate(v___x_1620_, v___x_1625_);
v___x_1627_ = lean_string_append(v___x_1626_, v___x_1620_);
return v___x_1627_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_sCall(lean_object* v_ret_1630_, lean_object* v_fn_1631_, lean_object* v_args_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1633_, 0, v_ret_1630_);
lean_ctor_set(v___x_1633_, 1, v_fn_1631_);
lean_ctor_set(v___x_1633_, 2, v_args_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_isCall(lean_object* v_x_1634_){
_start:
{
if (lean_obj_tag(v_x_1634_) == 5)
{
uint8_t v___x_1635_; 
v___x_1635_ = 1;
return v___x_1635_;
}
else
{
uint8_t v___x_1636_; 
v___x_1636_ = 0;
return v___x_1636_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_isCall___boxed(lean_object* v_x_1637_){
_start:
{
uint8_t v_res_1638_; lean_object* v_r_1639_; 
v_res_1638_ = lp_orb_x2dcompiler_Dsl_EmitPancake_PStmt_isCall(v_x_1637_);
lean_dec_ref(v_x_1637_);
v_r_1639_ = lean_box(v_res_1638_);
return v_r_1639_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(lean_object* v_l_1640_, lean_object* v_r_1641_){
_start:
{
uint8_t v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = 0;
v___x_1643_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_1643_, 0, v_l_1640_);
lean_ctor_set(v___x_1643_, 1, v_r_1641_);
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*2, v___x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eMul(lean_object* v_l_1644_, lean_object* v_r_1645_){
_start:
{
uint8_t v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = 1;
v___x_1647_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_1647_, 0, v_l_1644_);
lean_ctor_set(v___x_1647_, 1, v_r_1645_);
lean_ctor_set_uint8(v___x_1647_, sizeof(void*)*2, v___x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eLt(lean_object* v_l_1648_, lean_object* v_r_1649_){
_start:
{
uint8_t v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = 2;
v___x_1651_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_1651_, 0, v_l_1648_);
lean_ctor_set(v___x_1651_, 1, v_r_1649_);
lean_ctor_set_uint8(v___x_1651_, sizeof(void*)*2, v___x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eAnd(lean_object* v_l_1652_, lean_object* v_r_1653_){
_start:
{
uint8_t v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = 3;
v___x_1655_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_1655_, 0, v_l_1652_);
lean_ctor_set(v___x_1655_, 1, v_r_1653_);
lean_ctor_set_uint8(v___x_1655_, sizeof(void*)*2, v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eEq(lean_object* v_l_1656_, lean_object* v_r_1657_){
_start:
{
uint8_t v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = 4;
v___x_1659_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_1659_, 0, v_l_1656_);
lean_ctor_set(v___x_1659_, 1, v_r_1657_);
lean_ctor_set_uint8(v___x_1659_, sizeof(void*)*2, v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eLe(lean_object* v_l_1660_, lean_object* v_r_1661_){
_start:
{
uint8_t v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = 5;
v___x_1663_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_1663_, 0, v_l_1660_);
lean_ctor_set(v___x_1663_, 1, v_r_1661_);
lean_ctor_set_uint8(v___x_1663_, sizeof(void*)*2, v___x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eSub(lean_object* v_l_1664_, lean_object* v_r_1665_){
_start:
{
uint8_t v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = 6;
v___x_1667_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_1667_, 0, v_l_1664_);
lean_ctor_set(v___x_1667_, 1, v_r_1665_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*2, v___x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_v(lean_object* v_s_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1669_, 0, v_s_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_n(lean_object* v_k_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1671_, 0, v_k_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(lean_object* v_p_1672_, lean_object* v_k_1673_){
_start:
{
lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = lean_nat_dec_eq(v_k_1673_, v___x_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1676_, 0, v_k_1673_);
v___x_1677_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(v_p_1672_, v___x_1676_);
return v___x_1677_;
}
else
{
lean_dec(v_k_1673_);
return v_p_1672_;
}
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__3(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1681_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__2));
v___x_1682_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__1));
v___x_1683_ = lean_unsigned_to_nat(4294967295u);
v___x_1684_ = lean_unsigned_to_nat(16777215u);
v___x_1685_ = lean_unsigned_to_nat(31u);
v___x_1686_ = lean_unsigned_to_nat(4096u);
v___x_1687_ = lean_unsigned_to_nat(32u);
v___x_1688_ = lean_unsigned_to_nat(24u);
v___x_1689_ = lean_unsigned_to_nat(16u);
v___x_1690_ = lean_unsigned_to_nat(8u);
v___x_1691_ = lean_unsigned_to_nat(0u);
v___x_1692_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__0));
v___x_1693_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
lean_ctor_set(v___x_1693_, 1, v___x_1691_);
lean_ctor_set(v___x_1693_, 2, v___x_1690_);
lean_ctor_set(v___x_1693_, 3, v___x_1689_);
lean_ctor_set(v___x_1693_, 4, v___x_1688_);
lean_ctor_set(v___x_1693_, 5, v___x_1687_);
lean_ctor_set(v___x_1693_, 6, v___x_1686_);
lean_ctor_set(v___x_1693_, 7, v___x_1685_);
lean_ctor_set(v___x_1693_, 8, v___x_1684_);
lean_ctor_set(v___x_1693_, 9, v___x_1683_);
lean_ctor_set(v___x_1693_, 10, v___x_1682_);
lean_ctor_set(v___x_1693_, 11, v___x_1681_);
return v___x_1693_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0(void){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__3, &lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__3_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__3);
return v___x_1694_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__14(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__13));
v___x_1720_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__12));
v___x_1721_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(v___x_1720_, v___x_1719_);
return v___x_1721_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__15(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1722_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__14, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__14_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__14);
v___x_1723_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__11));
v___x_1724_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eLt(v___x_1723_, v___x_1722_);
return v___x_1724_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__21(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__13));
v___x_1736_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__20));
v___x_1737_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eLt(v___x_1736_, v___x_1735_);
return v___x_1737_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__23(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__12));
v___x_1741_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__4));
v___x_1742_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(v___x_1741_, v___x_1740_);
return v___x_1742_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__24(void){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__20));
v___x_1744_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__23, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__23_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__23);
v___x_1745_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(v___x_1744_, v___x_1743_);
return v___x_1745_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__25(void){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__24, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__24_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__24);
v___x_1747_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
return v___x_1747_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__27(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1750_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__26));
v___x_1751_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__20));
v___x_1752_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(v___x_1751_, v___x_1750_);
return v___x_1752_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__28(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__27, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__27_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__27);
v___x_1754_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__18));
v___x_1755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v___x_1753_);
return v___x_1755_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__29(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1756_ = lean_box(0);
v___x_1757_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__28, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__28_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__28);
v___x_1758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v___x_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion(lean_object* v_rs_1783_){
_start:
{
lean_object* v_name_1784_; lean_object* v_lenOff_1785_; lean_object* v_offViewOff_1786_; lean_object* v_viewLenOff_1787_; lean_object* v_resultOff_1788_; lean_object* v_bufOff_1789_; lean_object* v_arenaCap_1790_; lean_object* v_digestMul_1791_; lean_object* v_digestMask_1792_; lean_object* v_sentinel_1793_; lean_object* v_loadFfi_1794_; lean_object* v_reportFfi_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; lean_object* v___x_1868_; 
v_name_1784_ = lean_ctor_get(v_rs_1783_, 0);
lean_inc_ref(v_name_1784_);
v_lenOff_1785_ = lean_ctor_get(v_rs_1783_, 1);
lean_inc(v_lenOff_1785_);
v_offViewOff_1786_ = lean_ctor_get(v_rs_1783_, 2);
lean_inc(v_offViewOff_1786_);
v_viewLenOff_1787_ = lean_ctor_get(v_rs_1783_, 3);
lean_inc(v_viewLenOff_1787_);
v_resultOff_1788_ = lean_ctor_get(v_rs_1783_, 4);
lean_inc_n(v_resultOff_1788_, 2);
v_bufOff_1789_ = lean_ctor_get(v_rs_1783_, 5);
lean_inc(v_bufOff_1789_);
v_arenaCap_1790_ = lean_ctor_get(v_rs_1783_, 6);
lean_inc(v_arenaCap_1790_);
v_digestMul_1791_ = lean_ctor_get(v_rs_1783_, 7);
lean_inc(v_digestMul_1791_);
v_digestMask_1792_ = lean_ctor_get(v_rs_1783_, 8);
lean_inc(v_digestMask_1792_);
v_sentinel_1793_ = lean_ctor_get(v_rs_1783_, 9);
lean_inc(v_sentinel_1793_);
v_loadFfi_1794_ = lean_ctor_get(v_rs_1783_, 10);
lean_inc_ref(v_loadFfi_1794_);
v_reportFfi_1795_ = lean_ctor_get(v_rs_1783_, 11);
lean_inc_ref(v_reportFfi_1795_);
lean_dec_ref(v_rs_1783_);
v___x_1796_ = lean_box(0);
v___x_1797_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__1));
v___x_1798_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__2));
v___x_1799_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__3));
v___x_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1800_, 0, v_bufOff_1789_);
v___x_1801_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(v___x_1799_, v___x_1800_);
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1798_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1803_, 0, v_resultOff_1788_);
v___x_1804_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__4));
v___x_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1805_, 0, v_arenaCap_1790_);
v___x_1806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v___x_1796_);
v___x_1807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1804_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1803_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1799_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1810_, 0, v_loadFfi_1794_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__5));
v___x_1812_ = lean_unsigned_to_nat(1u);
v___x_1813_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_1799_, v_lenOff_1785_);
v___x_1814_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1811_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__6));
v___x_1817_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_1799_, v_offViewOff_1786_);
v___x_1818_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1812_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1816_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__7));
v___x_1821_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_1799_, v_viewLenOff_1787_);
v___x_1822_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1812_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1820_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__8));
v___x_1825_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__10));
v___x_1826_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__15);
v___x_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1827_, 0, v_sentinel_1793_);
v___x_1828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1824_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v___x_1796_);
v___x_1830_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__16));
v___x_1831_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__17));
v___x_1832_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__19));
v___x_1833_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__21, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__21_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__21);
v___x_1834_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__22));
v___x_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1835_, 0, v_digestMul_1791_);
v___x_1836_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eMul(v___x_1834_, v___x_1835_);
v___x_1837_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__25, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__25_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__25);
v___x_1838_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(v___x_1836_, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1839_, 0, v_digestMask_1792_);
v___x_1840_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAnd(v___x_1838_, v___x_1839_);
v___x_1841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1830_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__29, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__29_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__29);
v___x_1843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1841_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1833_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__31));
v___x_1846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1832_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1831_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1826_);
lean_ctor_set(v___x_1849_, 1, v___x_1829_);
lean_ctor_set(v___x_1849_, 2, v___x_1848_);
v___x_1850_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_1799_, v_resultOff_1788_);
v___x_1851_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__32));
lean_inc(v___x_1850_);
v___x_1852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__36));
v___x_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1850_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1855_, 0, v_reportFfi_1795_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__38));
v___x_1857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1852_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1849_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1825_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1823_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1819_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1815_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1810_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1802_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1797_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = 0;
v___x_1868_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1868_, 0, v_name_1784_);
lean_ctor_set(v___x_1868_, 1, v___x_1796_);
lean_ctor_set(v___x_1868_, 2, v___x_1866_);
lean_ctor_set_uint8(v___x_1868_, sizeof(void*)*3, v___x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun(lean_object* v_rs_1910_){
_start:
{
lean_object* v_name_1911_; lean_object* v_lenOff_1912_; lean_object* v_offViewOff_1913_; lean_object* v_digestMul_1914_; lean_object* v_digestMask_1915_; lean_object* v_sentinel_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; 
v_name_1911_ = lean_ctor_get(v_rs_1910_, 0);
lean_inc_ref(v_name_1911_);
v_lenOff_1912_ = lean_ctor_get(v_rs_1910_, 1);
lean_inc(v_lenOff_1912_);
v_offViewOff_1913_ = lean_ctor_get(v_rs_1910_, 2);
lean_inc(v_offViewOff_1913_);
v_digestMul_1914_ = lean_ctor_get(v_rs_1910_, 7);
lean_inc(v_digestMul_1914_);
v_digestMask_1915_ = lean_ctor_get(v_rs_1910_, 8);
lean_inc(v_digestMask_1915_);
v_sentinel_1916_ = lean_ctor_get(v_rs_1910_, 9);
lean_inc(v_sentinel_1916_);
lean_dec_ref(v_rs_1910_);
v___x_1917_ = lean_unsigned_to_nat(1u);
v___x_1918_ = lean_box(0);
v___x_1919_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__9));
v___x_1920_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__5));
v___x_1921_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__10));
v___x_1922_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_1921_, v_lenOff_1912_);
v___x_1923_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1917_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1920_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__6));
v___x_1926_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_1921_, v_offViewOff_1913_);
v___x_1927_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1917_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1925_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__8));
v___x_1930_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__10));
v___x_1931_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__15, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__15_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__15);
v___x_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1932_, 0, v_sentinel_1916_);
v___x_1933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1929_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
lean_ctor_set(v___x_1934_, 1, v___x_1918_);
v___x_1935_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__16));
v___x_1936_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__17));
v___x_1937_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__19));
v___x_1938_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__21, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__21_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__21);
v___x_1939_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__22));
v___x_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1940_, 0, v_digestMul_1914_);
v___x_1941_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eMul(v___x_1939_, v___x_1940_);
v___x_1942_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__25, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__25_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__25);
v___x_1943_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(v___x_1941_, v___x_1942_);
v___x_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1944_, 0, v_digestMask_1915_);
v___x_1945_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAnd(v___x_1943_, v___x_1944_);
v___x_1946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1935_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__29, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__29_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__29);
v___x_1948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1946_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1938_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__31));
v___x_1951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1937_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1936_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1931_);
lean_ctor_set(v___x_1954_, 1, v___x_1934_);
lean_ctor_set(v___x_1954_, 2, v___x_1953_);
v___x_1955_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__15));
v___x_1956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1954_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1930_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1928_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
v___x_1959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1924_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___x_1960_ = 1;
v___x_1961_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1961_, 0, v_name_1911_);
lean_ctor_set(v___x_1961_, 1, v___x_1919_);
lean_ctor_set(v___x_1961_, 2, v___x_1959_);
lean_ctor_set_uint8(v___x_1961_, sizeof(void*)*3, v___x_1960_);
return v___x_1961_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_boundscanExport(void){
_start:
{
lean_object* v___x_1963_; lean_object* v_offViewOff_1964_; lean_object* v_viewLenOff_1965_; lean_object* v_resultOff_1966_; lean_object* v_bufOff_1967_; lean_object* v_arenaCap_1968_; lean_object* v_digestMul_1969_; lean_object* v_digestMask_1970_; lean_object* v_sentinel_1971_; lean_object* v_loadFfi_1972_; lean_object* v_reportFfi_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1963_ = lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0;
v_offViewOff_1964_ = lean_ctor_get(v___x_1963_, 2);
v_viewLenOff_1965_ = lean_ctor_get(v___x_1963_, 3);
v_resultOff_1966_ = lean_ctor_get(v___x_1963_, 4);
v_bufOff_1967_ = lean_ctor_get(v___x_1963_, 5);
v_arenaCap_1968_ = lean_ctor_get(v___x_1963_, 6);
v_digestMul_1969_ = lean_ctor_get(v___x_1963_, 7);
v_digestMask_1970_ = lean_ctor_get(v___x_1963_, 8);
v_sentinel_1971_ = lean_ctor_get(v___x_1963_, 9);
v_loadFfi_1972_ = lean_ctor_get(v___x_1963_, 10);
v_reportFfi_1973_ = lean_ctor_get(v___x_1963_, 11);
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_boundscanExport___closed__0));
lean_inc_ref(v_reportFfi_1973_);
lean_inc_ref(v_loadFfi_1972_);
lean_inc(v_sentinel_1971_);
lean_inc(v_digestMask_1970_);
lean_inc(v_digestMul_1969_);
lean_inc(v_arenaCap_1968_);
lean_inc(v_bufOff_1967_);
lean_inc(v_resultOff_1966_);
lean_inc(v_viewLenOff_1965_);
lean_inc(v_offViewOff_1964_);
v___x_1976_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set(v___x_1976_, 1, v___x_1974_);
lean_ctor_set(v___x_1976_, 2, v_offViewOff_1964_);
lean_ctor_set(v___x_1976_, 3, v_viewLenOff_1965_);
lean_ctor_set(v___x_1976_, 4, v_resultOff_1966_);
lean_ctor_set(v___x_1976_, 5, v_bufOff_1967_);
lean_ctor_set(v___x_1976_, 6, v_arenaCap_1968_);
lean_ctor_set(v___x_1976_, 7, v_digestMul_1969_);
lean_ctor_set(v___x_1976_, 8, v_digestMask_1970_);
lean_ctor_set(v___x_1976_, 9, v_sentinel_1971_);
lean_ctor_set(v___x_1976_, 10, v_loadFfi_1972_);
lean_ctor_set(v___x_1976_, 11, v_reportFfi_1973_);
v___x_1977_ = lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun(v___x_1976_);
return v___x_1977_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__3(void){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__26));
v___x_1994_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__2));
v___x_1995_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eLt(v___x_1994_, v___x_1993_);
return v___x_1995_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__4(void){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1996_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__3, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__3_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__3);
v___x_1997_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__21, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__21_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__21);
v___x_1998_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAnd(v___x_1997_, v___x_1996_);
return v___x_1998_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__6(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2000_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__20));
v___x_2001_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__4));
v___x_2002_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(v___x_2001_, v___x_2000_);
return v___x_2002_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__7(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__6, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__6_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__6);
v___x_2004_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
return v___x_2004_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__8(void){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__7, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__7_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__7);
v___x_2006_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__5));
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
lean_ctor_set(v___x_2007_, 1, v___x_2005_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine(lean_object* v_ms_2019_){
_start:
{
lean_object* v_name_2020_; lean_object* v_viewLenOff_2021_; lean_object* v_resultOff_2022_; lean_object* v_bufOff_2023_; lean_object* v_arenaCap_2024_; lean_object* v_ctrlLen_2025_; lean_object* v_threshold_2026_; lean_object* v_loadFfi_2027_; lean_object* v_reportFfi_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; 
v_name_2020_ = lean_ctor_get(v_ms_2019_, 0);
lean_inc_ref(v_name_2020_);
v_viewLenOff_2021_ = lean_ctor_get(v_ms_2019_, 1);
lean_inc(v_viewLenOff_2021_);
v_resultOff_2022_ = lean_ctor_get(v_ms_2019_, 2);
lean_inc(v_resultOff_2022_);
v_bufOff_2023_ = lean_ctor_get(v_ms_2019_, 3);
lean_inc(v_bufOff_2023_);
v_arenaCap_2024_ = lean_ctor_get(v_ms_2019_, 4);
lean_inc(v_arenaCap_2024_);
v_ctrlLen_2025_ = lean_ctor_get(v_ms_2019_, 5);
lean_inc(v_ctrlLen_2025_);
v_threshold_2026_ = lean_ctor_get(v_ms_2019_, 6);
lean_inc(v_threshold_2026_);
v_loadFfi_2027_ = lean_ctor_get(v_ms_2019_, 7);
lean_inc_ref(v_loadFfi_2027_);
v_reportFfi_2028_ = lean_ctor_get(v_ms_2019_, 8);
lean_inc_ref(v_reportFfi_2028_);
lean_dec_ref(v_ms_2019_);
v___x_2029_ = lean_box(0);
v___x_2030_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__1));
v___x_2031_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__2));
v___x_2032_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__3));
v___x_2033_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_2032_, v_bufOff_2023_);
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2031_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_ctrlLen_2025_);
v___x_2036_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__4));
v___x_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2037_, 0, v_arenaCap_2024_);
v___x_2038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
lean_ctor_set(v___x_2038_, 1, v___x_2029_);
v___x_2039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2036_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
v___x_2040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2035_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
v___x_2041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2032_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2042_, 0, v_loadFfi_2027_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__7));
v___x_2044_ = lean_unsigned_to_nat(1u);
v___x_2045_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_2032_, v_viewLenOff_2021_);
v___x_2046_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2043_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
v___x_2048_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__19));
v___x_2049_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__1));
v___x_2050_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__4, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__4_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__4);
v___x_2051_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__8, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__8_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__8);
v___x_2052_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__9));
v___x_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2053_, 0, v_threshold_2026_);
v___x_2054_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eLt(v___x_2052_, v___x_2053_);
v___x_2055_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__11));
v___x_2056_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__29, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__29_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__29);
v___x_2057_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2054_);
lean_ctor_set(v___x_2057_, 1, v___x_2055_);
lean_ctor_set(v___x_2057_, 2, v___x_2056_);
v___x_2058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
lean_ctor_set(v___x_2058_, 1, v___x_2029_);
v___x_2059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2051_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2050_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__12));
v___x_2062_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_2032_, v_resultOff_2022_);
v___x_2063_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__32));
lean_inc(v___x_2062_);
v___x_2064_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2062_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__36));
v___x_2066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2062_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2067_, 0, v_reportFfi_2028_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__38));
v___x_2069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2064_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2061_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2060_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2049_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2048_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2047_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2042_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2034_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2030_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = 0;
v___x_2080_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2080_, 0, v_name_2020_);
lean_ctor_set(v___x_2080_, 1, v___x_2029_);
lean_ctor_set(v___x_2080_, 2, v___x_2078_);
lean_ctor_set_uint8(v___x_2080_, sizeof(void*)*3, v___x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_firstBelow(lean_object* v_thr_2081_, lean_object* v_a_2082_, lean_object* v_x_2083_, lean_object* v_x_2084_){
_start:
{
lean_object* v_zero_2085_; uint8_t v_isZero_2086_; 
v_zero_2085_ = lean_unsigned_to_nat(0u);
v_isZero_2086_ = lean_nat_dec_eq(v_x_2083_, v_zero_2085_);
if (v_isZero_2086_ == 1)
{
lean_dec(v_x_2083_);
return v_x_2084_;
}
else
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = lean_array_get_size(v_a_2082_);
v___x_2088_ = lean_nat_dec_le(v___x_2087_, v_x_2084_);
if (v___x_2088_ == 0)
{
uint8_t v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2089_ = l_instInhabitedUInt8;
v___x_2090_ = lean_box(v___x_2089_);
v___x_2091_ = lean_array_get(v___x_2090_, v_a_2082_, v_x_2084_);
lean_dec(v___x_2090_);
v___x_2092_ = lean_unbox(v___x_2091_);
lean_dec(v___x_2091_);
v___x_2093_ = lean_uint8_to_nat(v___x_2092_);
v___x_2094_ = lean_nat_dec_lt(v___x_2093_, v_thr_2081_);
if (v___x_2094_ == 0)
{
lean_object* v_one_2095_; lean_object* v_n_2096_; lean_object* v___x_2097_; 
v_one_2095_ = lean_unsigned_to_nat(1u);
v_n_2096_ = lean_nat_sub(v_x_2083_, v_one_2095_);
lean_dec(v_x_2083_);
v___x_2097_ = lean_nat_add(v_x_2084_, v_one_2095_);
lean_dec(v_x_2084_);
v_x_2083_ = v_n_2096_;
v_x_2084_ = v___x_2097_;
goto _start;
}
else
{
lean_dec(v_x_2083_);
return v_x_2084_;
}
}
else
{
lean_dec(v_x_2083_);
return v_x_2084_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_firstBelow___boxed(lean_object* v_thr_2099_, lean_object* v_a_2100_, lean_object* v_x_2101_, lean_object* v_x_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = lp_orb_x2dcompiler_Dsl_EmitPancake_firstBelow(v_thr_2099_, v_a_2100_, v_x_2101_, v_x_2102_);
lean_dec_ref(v_a_2100_);
lean_dec(v_thr_2099_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_tokenScanSpec(lean_object* v_ms_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_threshold_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v_threshold_2106_ = lean_ctor_get(v_ms_2104_, 6);
v___x_2107_ = lean_array_get_size(v_a_2105_);
v___x_2108_ = lean_unsigned_to_nat(0u);
v___x_2109_ = lp_orb_x2dcompiler_Dsl_EmitPancake_firstBelow(v_threshold_2106_, v_a_2105_, v___x_2107_, v___x_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_tokenScanSpec___boxed(lean_object* v_ms_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = lp_orb_x2dcompiler_Dsl_EmitPancake_tokenScanSpec(v_ms_2110_, v_a_2111_);
lean_dec_ref(v_a_2111_);
lean_dec_ref(v_ms_2110_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2113_, lean_object* v_x_2114_, lean_object* v_x_2115_){
_start:
{
if (lean_obj_tag(v_x_2115_) == 0)
{
lean_dec(v_x_2113_);
return v_x_2114_;
}
else
{
lean_object* v_head_2116_; lean_object* v_tail_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2127_; 
v_head_2116_ = lean_ctor_get(v_x_2115_, 0);
v_tail_2117_ = lean_ctor_get(v_x_2115_, 1);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_x_2115_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2119_ = v_x_2115_;
v_isShared_2120_ = v_isSharedCheck_2127_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_tail_2117_);
lean_inc(v_head_2116_);
lean_dec(v_x_2115_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2127_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
lean_inc(v_x_2113_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set_tag(v___x_2119_, 5);
lean_ctor_set(v___x_2119_, 1, v_x_2113_);
lean_ctor_set(v___x_2119_, 0, v_x_2114_);
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_x_2114_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_x_2113_);
v___x_2122_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg(v_head_2116_);
v___x_2124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v_x_2114_ = v___x_2124_;
v_x_2115_ = v_tail_2117_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0_spec__0_spec__1(lean_object* v_x_2128_, lean_object* v_x_2129_, lean_object* v_x_2130_){
_start:
{
if (lean_obj_tag(v_x_2130_) == 0)
{
lean_dec(v_x_2128_);
return v_x_2129_;
}
else
{
lean_object* v_head_2131_; lean_object* v_tail_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2142_; 
v_head_2131_ = lean_ctor_get(v_x_2130_, 0);
v_tail_2132_ = lean_ctor_get(v_x_2130_, 1);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_x_2130_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2134_ = v_x_2130_;
v_isShared_2135_ = v_isSharedCheck_2142_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_tail_2132_);
lean_inc(v_head_2131_);
lean_dec(v_x_2130_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2142_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
lean_inc(v_x_2128_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set_tag(v___x_2134_, 5);
lean_ctor_set(v___x_2134_, 1, v_x_2128_);
lean_ctor_set(v___x_2134_, 0, v_x_2129_);
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_x_2129_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_x_2128_);
v___x_2137_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg(v_head_2131_);
v___x_2139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2137_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = lp_orb_x2dcompiler_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0_spec__0_spec__1_spec__2(v_x_2128_, v___x_2139_, v_tail_2132_);
return v___x_2140_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0_spec__0(lean_object* v_x_2143_, lean_object* v_x_2144_){
_start:
{
if (lean_obj_tag(v_x_2143_) == 0)
{
lean_object* v___x_2145_; 
lean_dec(v_x_2144_);
v___x_2145_ = lean_box(0);
return v___x_2145_;
}
else
{
lean_object* v_tail_2146_; 
v_tail_2146_ = lean_ctor_get(v_x_2143_, 1);
if (lean_obj_tag(v_tail_2146_) == 0)
{
lean_object* v_head_2147_; lean_object* v___x_2148_; 
lean_dec(v_x_2144_);
v_head_2147_ = lean_ctor_get(v_x_2143_, 0);
lean_inc(v_head_2147_);
lean_dec_ref(v_x_2143_);
v___x_2148_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg(v_head_2147_);
return v___x_2148_;
}
else
{
lean_object* v_head_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_inc(v_tail_2146_);
v_head_2149_ = lean_ctor_get(v_x_2143_, 0);
lean_inc(v_head_2149_);
lean_dec_ref(v_x_2143_);
v___x_2150_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg(v_head_2149_);
v___x_2151_ = lp_orb_x2dcompiler_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0_spec__0_spec__1(v_x_2144_, v___x_2150_, v_tail_2146_);
return v___x_2151_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0___redArg(lean_object* v_a_2152_){
_start:
{
if (lean_obj_tag(v_a_2152_) == 0)
{
lean_object* v___x_2153_; 
v___x_2153_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__1));
return v___x_2153_;
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; lean_object* v___x_2163_; 
v___x_2154_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__5));
v___x_2155_ = lp_orb_x2dcompiler_Std_Format_joinSep___at___00List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0_spec__0(v_a_2152_, v___x_2154_);
v___x_2156_ = lean_obj_once(&lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8, &lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8_once, _init_lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__8);
v___x_2157_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__9));
v___x_2158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
lean_ctor_set(v___x_2158_, 1, v___x_2155_);
v___x_2159_ = ((lean_object*)(lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPStmt_repr_spec__0___redArg___closed__10));
v___x_2160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2158_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2156_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = 0;
v___x_2163_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set_uint8(v___x_2163_, sizeof(void*)*1, v___x_2162_);
return v___x_2163_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg(lean_object* v_x_2173_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2174_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg___closed__3));
v___x_2175_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__7, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__7_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__7);
v___x_2176_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0___redArg(v_x_2173_);
v___x_2177_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2175_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = 0;
v___x_2179_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2179_, 0, v___x_2177_);
lean_ctor_set_uint8(v___x_2179_, sizeof(void*)*1, v___x_2178_);
v___x_2180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2174_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__18, &lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__18_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__18);
v___x_2182_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__19));
v___x_2183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
lean_ctor_set(v___x_2183_, 1, v___x_2180_);
v___x_2184_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPFun_repr___redArg___closed__20));
v___x_2185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2183_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2181_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
lean_ctor_set_uint8(v___x_2187_, sizeof(void*)*1, v___x_2178_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr(lean_object* v_x_2188_, lean_object* v_prec_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___redArg(v_x_2188_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr___boxed(lean_object* v_x_2191_, lean_object* v_prec_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = lp_orb_x2dcompiler_Dsl_EmitPancake_instReprPProgram_repr(v_x_2191_, v_prec_2192_);
lean_dec(v_prec_2192_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0(lean_object* v_a_2194_, lean_object* v_n_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0___redArg(v_a_2194_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0___boxed(lean_object* v_a_2197_, lean_object* v_n_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = lp_orb_x2dcompiler_List_repr___at___00Dsl_EmitPancake_instReprPProgram_repr_spec__0(v_a_2197_, v_n_2198_);
lean_dec(v_n_2198_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_ppProgram_spec__0(lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
if (lean_obj_tag(v_a_2202_) == 0)
{
lean_object* v___x_2204_; 
v___x_2204_ = l_List_reverse___redArg(v_a_2203_);
return v___x_2204_;
}
else
{
lean_object* v_head_2205_; lean_object* v_tail_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2215_; 
v_head_2205_ = lean_ctor_get(v_a_2202_, 0);
v_tail_2206_ = lean_ctor_get(v_a_2202_, 1);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_a_2202_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2208_ = v_a_2202_;
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_tail_2206_);
lean_inc(v_head_2205_);
lean_dec(v_a_2202_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2210_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun(v_head_2205_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 1, v_a_2203_);
lean_ctor_set(v___x_2208_, 0, v___x_2210_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2210_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_a_2203_);
v___x_2212_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
v_a_2202_ = v_tail_2206_;
v_a_2203_ = v___x_2212_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppProgram(lean_object* v_p_2216_){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2217_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__1));
v___x_2218_ = lean_box(0);
v___x_2219_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_ppProgram_spec__0(v_p_2216_, v___x_2218_);
v___x_2220_ = l_String_intercalate(v___x_2217_, v___x_2219_);
return v___x_2220_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__10(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__26));
v___x_2246_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__7));
v___x_2247_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(v___x_2246_, v___x_2245_);
return v___x_2247_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__11(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2248_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__10, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__10_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__10);
v___x_2249_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__5));
v___x_2250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
lean_ctor_set(v___x_2250_, 1, v___x_2248_);
return v___x_2250_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__12(void){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__11, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__11_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__11);
v___x_2253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
lean_ctor_set(v___x_2253_, 1, v___x_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage(lean_object* v_cs_2259_){
_start:
{
lean_object* v_name_2260_; lean_object* v_fieldOff_2261_; lean_object* v_threshold_2262_; lean_object* v_satMax_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; uint8_t v___x_2298_; lean_object* v___x_2299_; 
v_name_2260_ = lean_ctor_get(v_cs_2259_, 0);
lean_inc_ref(v_name_2260_);
v_fieldOff_2261_ = lean_ctor_get(v_cs_2259_, 1);
lean_inc(v_fieldOff_2261_);
v_threshold_2262_ = lean_ctor_get(v_cs_2259_, 2);
lean_inc(v_threshold_2262_);
v_satMax_2263_ = lean_ctor_get(v_cs_2259_, 3);
lean_inc(v_satMax_2263_);
lean_dec_ref(v_cs_2259_);
v___x_2264_ = lean_unsigned_to_nat(1u);
v___x_2265_ = lean_box(0);
v___x_2266_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__4));
v___x_2267_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__5));
v___x_2268_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__6));
v___x_2269_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_2268_, v_fieldOff_2261_);
lean_inc(v___x_2269_);
v___x_2270_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2264_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2267_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__19));
v___x_2273_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__21, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__21_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__21);
v___x_2274_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__8, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__8_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__8);
v___x_2275_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine___closed__9));
v___x_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2276_, 0, v_threshold_2262_);
v___x_2277_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eLt(v___x_2275_, v___x_2276_);
v___x_2278_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__7));
v___x_2279_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__9));
v___x_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2280_, 0, v_satMax_2263_);
lean_inc_ref(v___x_2280_);
v___x_2281_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eLt(v___x_2278_, v___x_2280_);
v___x_2282_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__12, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__12_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__12);
v___x_2283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2267_);
lean_ctor_set(v___x_2283_, 1, v___x_2280_);
v___x_2284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
lean_ctor_set(v___x_2284_, 1, v___x_2265_);
v___x_2285_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2281_);
lean_ctor_set(v___x_2285_, 1, v___x_2282_);
lean_ctor_set(v___x_2285_, 2, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
lean_ctor_set(v___x_2286_, 1, v___x_2265_);
v___x_2287_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2277_);
lean_ctor_set(v___x_2287_, 1, v___x_2279_);
lean_ctor_set(v___x_2287_, 2, v___x_2286_);
v___x_2288_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__29, &lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__29_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__29);
v___x_2289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2274_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2273_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2269_);
lean_ctor_set(v___x_2292_, 1, v___x_2278_);
v___x_2293_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__14));
v___x_2294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2292_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
v___x_2295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2291_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
v___x_2296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2272_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2271_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = 0;
v___x_2299_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2299_, 0, v_name_2260_);
lean_ctor_set(v___x_2299_, 1, v___x_2266_);
lean_ctor_set(v___x_2299_, 2, v___x_2297_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*3, v___x_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage(lean_object* v_cs_2311_){
_start:
{
lean_object* v_name_2312_; lean_object* v_admitOff_2313_; lean_object* v_mirrorOff_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; lean_object* v___x_2329_; 
v_name_2312_ = lean_ctor_get(v_cs_2311_, 0);
lean_inc_ref(v_name_2312_);
v_admitOff_2313_ = lean_ctor_get(v_cs_2311_, 1);
lean_inc(v_admitOff_2313_);
v_mirrorOff_2314_ = lean_ctor_get(v_cs_2311_, 2);
lean_inc(v_mirrorOff_2314_);
lean_dec_ref(v_cs_2311_);
v___x_2315_ = lean_unsigned_to_nat(1u);
v___x_2316_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__0));
v___x_2317_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__1));
v___x_2318_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__6));
v___x_2319_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_2318_, v_admitOff_2313_);
v___x_2320_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2315_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2317_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_2318_, v_mirrorOff_2314_);
v___x_2323_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__2));
v___x_2324_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2322_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage___closed__4));
v___x_2326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
v___x_2327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2321_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = 0;
v___x_2329_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2329_, 0, v_name_2312_);
lean_ctor_set(v___x_2329_, 1, v___x_2316_);
lean_ctor_set(v___x_2329_, 2, v___x_2327_);
lean_ctor_set_uint8(v___x_2329_, sizeof(void*)*3, v___x_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_emitServeMain_spec__0(lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
if (lean_obj_tag(v_a_2330_) == 0)
{
lean_object* v___x_2332_; 
v___x_2332_ = l_List_reverse___redArg(v_a_2331_);
return v___x_2332_;
}
else
{
lean_object* v_head_2333_; lean_object* v_tail_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2354_; 
v_head_2333_ = lean_ctor_get(v_a_2330_, 0);
v_tail_2334_ = lean_ctor_get(v_a_2330_, 1);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_a_2330_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2336_ = v_a_2330_;
v_isShared_2337_ = v_isSharedCheck_2354_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_tail_2334_);
lean_inc(v_head_2333_);
lean_dec(v_a_2330_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2354_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v_fst_2338_; lean_object* v_snd_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2353_; 
v_fst_2338_ = lean_ctor_get(v_head_2333_, 0);
v_snd_2339_ = lean_ctor_get(v_head_2333_, 1);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_head_2333_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2341_ = v_head_2333_;
v_isShared_2342_ = v_isSharedCheck_2353_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_snd_2339_);
lean_inc(v_fst_2338_);
lean_dec(v_head_2333_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2353_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2343_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__6));
v___x_2344_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_2343_, v_fst_2338_);
v___x_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2345_, 0, v_snd_2339_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set_tag(v___x_2341_, 2);
lean_ctor_set(v___x_2341_, 1, v___x_2345_);
lean_ctor_set(v___x_2341_, 0, v___x_2344_);
v___x_2347_ = v___x_2341_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2349_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 1, v_a_2331_);
lean_ctor_set(v___x_2336_, 0, v___x_2347_);
v___x_2349_ = v___x_2336_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_a_2331_);
v___x_2349_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
v_a_2330_ = v_tail_2334_;
v_a_2331_ = v___x_2349_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Dsl_EmitPancake_emitServeMain_spec__3(lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
if (lean_obj_tag(v_a_2355_) == 0)
{
lean_object* v___x_2357_; 
v___x_2357_ = lean_array_to_list(v_a_2356_);
return v___x_2357_;
}
else
{
lean_object* v_head_2358_; lean_object* v_tail_2359_; lean_object* v___x_2360_; 
v_head_2358_ = lean_ctor_get(v_a_2355_, 0);
lean_inc(v_head_2358_);
v_tail_2359_ = lean_ctor_get(v_a_2355_, 1);
lean_inc(v_tail_2359_);
lean_dec_ref(v_a_2355_);
v___x_2360_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2356_, v_head_2358_);
v_a_2355_ = v_tail_2359_;
v_a_2356_ = v___x_2360_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_emitServeMain_spec__2(lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
if (lean_obj_tag(v_a_2363_) == 0)
{
lean_object* v___x_2365_; 
v___x_2365_ = l_List_reverse___redArg(v_a_2364_);
return v___x_2365_;
}
else
{
lean_object* v_head_2366_; lean_object* v_tail_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2398_; 
v_head_2366_ = lean_ctor_get(v_a_2363_, 0);
v_tail_2367_ = lean_ctor_get(v_a_2363_, 1);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_a_2363_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2369_ = v_a_2363_;
v_isShared_2370_ = v_isSharedCheck_2398_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_tail_2367_);
lean_inc(v_head_2366_);
lean_dec(v_a_2363_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2398_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v_fst_2371_; lean_object* v_snd_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2397_; 
v_fst_2371_ = lean_ctor_get(v_head_2366_, 0);
v_snd_2372_ = lean_ctor_get(v_head_2366_, 1);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_head_2366_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2374_ = v_head_2366_;
v_isShared_2375_ = v_isSharedCheck_2397_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_snd_2372_);
lean_inc(v_fst_2371_);
lean_dec(v_head_2366_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2397_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v_nm_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2376_ = lean_unsigned_to_nat(1u);
v___x_2377_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__10));
v___x_2378_ = lean_box(0);
v___x_2379_ = ((lean_object*)(lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_emitServeMain_spec__2___closed__0));
lean_inc(v_fst_2371_);
v___x_2380_ = l_Nat_reprFast(v_fst_2371_);
v_nm_2381_ = lean_string_append(v___x_2379_, v___x_2380_);
lean_dec_ref(v___x_2380_);
v___x_2382_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__6));
v___x_2383_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_2382_, v_snd_2372_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set_tag(v___x_2374_, 4);
lean_ctor_set(v___x_2374_, 1, v___x_2383_);
lean_ctor_set(v___x_2374_, 0, v___x_2376_);
v___x_2385_ = v___x_2374_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
lean_inc_ref(v_nm_2381_);
v___x_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2386_, 0, v_nm_2381_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_2377_, v_fst_2371_);
v___x_2388_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2388_, 0, v_nm_2381_);
v___x_2389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2387_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 1, v___x_2378_);
lean_ctor_set(v___x_2369_, 0, v___x_2389_);
v___x_2391_ = v___x_2369_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2389_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v___x_2378_);
v___x_2391_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2386_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
lean_ctor_set(v___x_2393_, 1, v_a_2364_);
v_a_2363_ = v_tail_2367_;
v_a_2364_ = v___x_2393_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_emitServeMain_spec__1(lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
if (lean_obj_tag(v_a_2399_) == 0)
{
lean_object* v___x_2401_; 
v___x_2401_ = l_List_reverse___redArg(v_a_2400_);
return v___x_2401_;
}
else
{
lean_object* v_head_2402_; lean_object* v_snd_2403_; lean_object* v_tail_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2416_; 
v_head_2402_ = lean_ctor_get(v_a_2399_, 0);
lean_inc(v_head_2402_);
v_snd_2403_ = lean_ctor_get(v_head_2402_, 1);
lean_inc(v_snd_2403_);
v_tail_2404_ = lean_ctor_get(v_a_2399_, 1);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_a_2399_);
if (v_isSharedCheck_2416_ == 0)
{
lean_object* v_unused_2417_; 
v_unused_2417_ = lean_ctor_get(v_a_2399_, 0);
lean_dec(v_unused_2417_);
v___x_2406_ = v_a_2399_;
v_isShared_2407_ = v_isSharedCheck_2416_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_tail_2404_);
lean_dec(v_a_2399_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2416_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v_fst_2408_; lean_object* v_fst_2409_; lean_object* v_snd_2410_; lean_object* v___x_2411_; lean_object* v___x_2413_; 
v_fst_2408_ = lean_ctor_get(v_head_2402_, 0);
lean_inc(v_fst_2408_);
lean_dec(v_head_2402_);
v_fst_2409_ = lean_ctor_get(v_snd_2403_, 0);
lean_inc(v_fst_2409_);
v_snd_2410_ = lean_ctor_get(v_snd_2403_, 1);
lean_inc(v_snd_2410_);
lean_dec(v_snd_2403_);
v___x_2411_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_2411_, 0, v_fst_2408_);
lean_ctor_set(v___x_2411_, 1, v_fst_2409_);
lean_ctor_set(v___x_2411_, 2, v_snd_2410_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 1, v_a_2400_);
lean_ctor_set(v___x_2406_, 0, v___x_2411_);
v___x_2413_ = v___x_2406_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v_a_2400_);
v___x_2413_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
v_a_2399_ = v_tail_2404_;
v_a_2400_ = v___x_2413_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_emitServeMain(lean_object* v_spec_2423_, lean_object* v_calls_2424_){
_start:
{
lean_object* v_loadFfi_2425_; lean_object* v_reportFfi_2426_; lean_object* v_ctrlLen_2427_; lean_object* v_loadCap_2428_; lean_object* v_lenOff_2429_; lean_object* v_respOff_2430_; lean_object* v_bufOff_2431_; lean_object* v_reportOff_2432_; lean_object* v_reportLen_2433_; lean_object* v_respInit_2434_; lean_object* v_mirror_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; lean_object* v___x_2483_; 
v_loadFfi_2425_ = lean_ctor_get(v_spec_2423_, 0);
lean_inc_ref(v_loadFfi_2425_);
v_reportFfi_2426_ = lean_ctor_get(v_spec_2423_, 1);
lean_inc_ref(v_reportFfi_2426_);
v_ctrlLen_2427_ = lean_ctor_get(v_spec_2423_, 2);
lean_inc(v_ctrlLen_2427_);
v_loadCap_2428_ = lean_ctor_get(v_spec_2423_, 3);
lean_inc(v_loadCap_2428_);
v_lenOff_2429_ = lean_ctor_get(v_spec_2423_, 4);
lean_inc(v_lenOff_2429_);
v_respOff_2430_ = lean_ctor_get(v_spec_2423_, 5);
lean_inc(v_respOff_2430_);
v_bufOff_2431_ = lean_ctor_get(v_spec_2423_, 6);
lean_inc(v_bufOff_2431_);
v_reportOff_2432_ = lean_ctor_get(v_spec_2423_, 7);
lean_inc(v_reportOff_2432_);
v_reportLen_2433_ = lean_ctor_get(v_spec_2423_, 8);
lean_inc(v_reportLen_2433_);
v_respInit_2434_ = lean_ctor_get(v_spec_2423_, 9);
lean_inc(v_respInit_2434_);
v_mirror_2435_ = lean_ctor_get(v_spec_2423_, 10);
lean_inc(v_mirror_2435_);
lean_dec_ref(v_spec_2423_);
v___x_2436_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitServeMain___closed__0));
v___x_2437_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0___closed__0));
v___x_2438_ = lean_box(0);
v___x_2439_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage___closed__0));
v___x_2440_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitExportFun___closed__10));
v___x_2441_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_2440_, v_respOff_2430_);
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2439_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__2));
v___x_2444_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_2440_, v_bufOff_2431_);
v___x_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2443_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
v___x_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2446_, 0, v_ctrlLen_2427_);
v___x_2447_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__4));
v___x_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2448_, 0, v_loadCap_2428_);
v___x_2449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
lean_ctor_set(v___x_2449_, 1, v___x_2438_);
v___x_2450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2447_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2446_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2440_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2453_, 0, v_loadFfi_2425_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__7));
v___x_2455_ = lean_unsigned_to_nat(1u);
v___x_2456_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_2440_, v_lenOff_2429_);
v___x_2457_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2455_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2454_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
lean_ctor_set(v___x_2459_, 1, v___x_2438_);
v___x_2460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2453_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2445_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2442_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2436_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_emitServeMain_spec__0(v_respInit_2434_, v___x_2438_);
v___x_2465_ = l_List_appendTR___redArg(v___x_2463_, v___x_2464_);
v___x_2466_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_emitServeMain_spec__1(v_calls_2424_, v___x_2438_);
v___x_2467_ = l_List_appendTR___redArg(v___x_2465_, v___x_2466_);
v___x_2468_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_emitServeMain_spec__2(v_mirror_2435_, v___x_2438_);
v___x_2469_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitServeMain___closed__1));
v___x_2470_ = lp_orb_x2dcompiler___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Dsl_EmitPancake_emitServeMain_spec__3(v___x_2468_, v___x_2469_);
v___x_2471_ = l_List_appendTR___redArg(v___x_2467_, v___x_2470_);
v___x_2472_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_2440_, v_reportOff_2432_);
v___x_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2473_, 0, v_reportLen_2433_);
lean_inc_ref(v___x_2473_);
v___x_2474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
lean_ctor_set(v___x_2474_, 1, v___x_2438_);
v___x_2475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2440_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2473_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
v___x_2477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2472_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2478_, 0, v_reportFfi_2426_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion___closed__38));
v___x_2480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2478_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = l_List_appendTR___redArg(v___x_2471_, v___x_2480_);
v___x_2482_ = 0;
v___x_2483_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2483_, 0, v___x_2437_);
lean_ctor_set(v___x_2483_, 1, v___x_2438_);
lean_ctor_set(v___x_2483_, 2, v___x_2481_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*3, v___x_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_fuse_spec__1(lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
if (lean_obj_tag(v_a_2484_) == 0)
{
lean_object* v___x_2486_; 
v___x_2486_ = l_List_reverse___redArg(v_a_2485_);
return v___x_2486_;
}
else
{
lean_object* v_head_2487_; lean_object* v_fn_2488_; lean_object* v_tail_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2502_; 
v_head_2487_ = lean_ctor_get(v_a_2484_, 0);
lean_inc(v_head_2487_);
v_fn_2488_ = lean_ctor_get(v_head_2487_, 0);
lean_inc_ref(v_fn_2488_);
v_tail_2489_ = lean_ctor_get(v_a_2484_, 1);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_a_2484_);
if (v_isSharedCheck_2502_ == 0)
{
lean_object* v_unused_2503_; 
v_unused_2503_ = lean_ctor_get(v_a_2484_, 0);
lean_dec(v_unused_2503_);
v___x_2491_ = v_a_2484_;
v_isShared_2492_ = v_isSharedCheck_2502_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_tail_2489_);
lean_dec(v_a_2484_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2502_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v_bind_2493_; lean_object* v_args_2494_; lean_object* v_name_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
v_bind_2493_ = lean_ctor_get(v_head_2487_, 1);
lean_inc_ref(v_bind_2493_);
v_args_2494_ = lean_ctor_get(v_head_2487_, 2);
lean_inc(v_args_2494_);
lean_dec(v_head_2487_);
v_name_2495_ = lean_ctor_get(v_fn_2488_, 0);
lean_inc_ref(v_name_2495_);
lean_dec_ref(v_fn_2488_);
v___x_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2496_, 0, v_name_2495_);
lean_ctor_set(v___x_2496_, 1, v_args_2494_);
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v_bind_2493_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 1, v_a_2485_);
lean_ctor_set(v___x_2491_, 0, v___x_2497_);
v___x_2499_ = v___x_2491_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_a_2485_);
v___x_2499_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
v_a_2484_ = v_tail_2489_;
v_a_2485_ = v___x_2499_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_fuse_spec__0(lean_object* v_a_2504_, lean_object* v_a_2505_){
_start:
{
if (lean_obj_tag(v_a_2504_) == 0)
{
lean_object* v___x_2506_; 
v___x_2506_ = l_List_reverse___redArg(v_a_2505_);
return v___x_2506_;
}
else
{
lean_object* v_head_2507_; lean_object* v_tail_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2517_; 
v_head_2507_ = lean_ctor_get(v_a_2504_, 0);
v_tail_2508_ = lean_ctor_get(v_a_2504_, 1);
v_isSharedCheck_2517_ = !lean_is_exclusive(v_a_2504_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2510_ = v_a_2504_;
v_isShared_2511_ = v_isSharedCheck_2517_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_tail_2508_);
lean_inc(v_head_2507_);
lean_dec(v_a_2504_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2517_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v_fn_2512_; lean_object* v___x_2514_; 
v_fn_2512_ = lean_ctor_get(v_head_2507_, 0);
lean_inc_ref(v_fn_2512_);
lean_dec(v_head_2507_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 1, v_a_2505_);
lean_ctor_set(v___x_2510_, 0, v_fn_2512_);
v___x_2514_ = v___x_2510_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_fn_2512_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_a_2505_);
v___x_2514_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
v_a_2504_ = v_tail_2508_;
v_a_2505_ = v___x_2514_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_fuse(lean_object* v_spec_2518_, lean_object* v_stages_2519_){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2520_ = lean_box(0);
lean_inc(v_stages_2519_);
v___x_2521_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_fuse_spec__0(v_stages_2519_, v___x_2520_);
v___x_2522_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Dsl_EmitPancake_fuse_spec__1(v_stages_2519_, v___x_2520_);
v___x_2523_ = lp_orb_x2dcompiler_Dsl_EmitPancake_emitServeMain(v_spec_2518_, v___x_2522_);
v___x_2524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
lean_ctor_set(v___x_2524_, 1, v___x_2520_);
v___x_2525_ = l_List_appendTR___redArg(v___x_2521_, v___x_2524_);
return v___x_2525_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__39(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__38));
v___x_2646_ = lp_orb_x2dcompiler_Dsl_EmitPancake_emitCounterStage(v___x_2645_);
return v___x_2646_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__44(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2657_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__43));
v___x_2658_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__40));
v___x_2659_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__39, &lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__39_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__39);
v___x_2660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
lean_ctor_set(v___x_2660_, 1, v___x_2658_);
lean_ctor_set(v___x_2660_, 2, v___x_2657_);
return v___x_2660_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__47(void){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__46));
v___x_2667_ = lp_orb_x2dcompiler_Dsl_EmitPancake_emitCombineStage(v___x_2666_);
return v___x_2667_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__50(void){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2672_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__49));
v___x_2673_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__48));
v___x_2674_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__47, &lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__47_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__47);
v___x_2675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
lean_ctor_set(v___x_2675_, 1, v___x_2673_);
lean_ctor_set(v___x_2675_, 2, v___x_2672_);
return v___x_2675_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__51(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = lean_box(0);
v___x_2677_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__50, &lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__50_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__50);
v___x_2678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
lean_ctor_set(v___x_2678_, 1, v___x_2676_);
return v___x_2678_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__52(void){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__51, &lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__51_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__51);
v___x_2680_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__44, &lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__44_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__44);
v___x_2681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
lean_ctor_set(v___x_2681_, 1, v___x_2679_);
return v___x_2681_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__53(void){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2682_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__52, &lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__52_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__52);
v___x_2683_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__36));
v___x_2684_ = lp_orb_x2dcompiler_Dsl_EmitPancake_fuse(v___x_2683_, v___x_2682_);
return v___x_2684_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice(void){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__53, &lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__53_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice___closed__53);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_banner(lean_object* v_what_2688_){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2689_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_banner___closed__0));
v___x_2690_ = lean_string_append(v___x_2689_, v_what_2688_);
v___x_2691_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun___closed__1));
v___x_2692_ = lean_string_append(v___x_2690_, v___x_2691_);
v___x_2693_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_banner___closed__1));
v___x_2694_ = lean_string_append(v___x_2692_, v___x_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_banner___boxed(lean_object* v_what_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = lp_orb_x2dcompiler_Dsl_EmitPancake_banner(v_what_2695_);
lean_dec_ref(v_what_2695_);
return v_res_2696_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__1(void){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__0));
v___x_2699_ = lp_orb_x2dcompiler_Dsl_EmitPancake_banner(v___x_2698_);
return v___x_2699_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__2(void){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0;
v___x_2701_ = lp_orb_x2dcompiler_Dsl_EmitPancake_emitRegion(v___x_2700_);
return v___x_2701_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__3(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__2, &lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__2_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__2);
v___x_2703_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun(v___x_2702_);
return v___x_2703_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__4(void){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__3, &lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__3_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__3);
v___x_2705_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__1, &lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__1_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__1);
v___x_2706_ = lean_string_append(v___x_2705_, v___x_2704_);
return v___x_2706_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk(void){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__4, &lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__4_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk___closed__4);
return v___x_2707_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__1(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__0));
v___x_2710_ = lp_orb_x2dcompiler_Dsl_EmitPancake_banner(v___x_2709_);
return v___x_2710_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__2(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_machineC0));
v___x_2712_ = lp_orb_x2dcompiler_Dsl_EmitPancake_emitMachine(v___x_2711_);
return v___x_2712_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__3(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__2, &lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__2_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__2);
v___x_2714_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun(v___x_2713_);
return v___x_2714_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__4(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__3, &lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__3_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__3);
v___x_2716_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__1, &lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__1_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__1);
v___x_2717_ = lean_string_append(v___x_2716_, v___x_2715_);
return v___x_2717_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk(void){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__4, &lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__4_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk___closed__4);
return v___x_2718_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__1(void){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__0));
v___x_2721_ = lp_orb_x2dcompiler_Dsl_EmitPancake_banner(v___x_2720_);
return v___x_2721_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__2(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = lp_orb_x2dcompiler_Dsl_EmitPancake_boundscanExport;
v___x_2723_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun(v___x_2722_);
return v___x_2723_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__3(void){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2724_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__2, &lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__2_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__2);
v___x_2725_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__1, &lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__1_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__1);
v___x_2726_ = lean_string_append(v___x_2725_, v___x_2724_);
return v___x_2726_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk(void){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__3, &lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__3_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk___closed__3);
return v___x_2727_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__1(void){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2729_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__0));
v___x_2730_ = lp_orb_x2dcompiler_Dsl_EmitPancake_banner(v___x_2729_);
return v___x_2730_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__2(void){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice;
v___x_2732_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppProgram(v___x_2731_);
return v___x_2732_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__3(void){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__2, &lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__2_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__2);
v___x_2734_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__1, &lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__1_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__1);
v___x_2735_ = lean_string_append(v___x_2734_, v___x_2733_);
return v___x_2735_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk(void){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = lean_obj_once(&lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__3, &lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__3_once, _init_lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk___closed__3);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_IO_print___at___00IO_println___at___00Dsl_EmitPancake_main_spec__0_spec__0(lean_object* v_s_2737_){
_start:
{
lean_object* v___x_2739_; lean_object* v_putStr_2740_; lean_object* v___x_2741_; 
v___x_2739_ = lean_get_stdout();
v_putStr_2740_ = lean_ctor_get(v___x_2739_, 4);
lean_inc_ref(v_putStr_2740_);
lean_dec_ref(v___x_2739_);
v___x_2741_ = lean_apply_2(v_putStr_2740_, v_s_2737_, lean_box(0));
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_IO_print___at___00IO_println___at___00Dsl_EmitPancake_main_spec__0_spec__0___boxed(lean_object* v_s_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = lp_orb_x2dcompiler_IO_print___at___00IO_println___at___00Dsl_EmitPancake_main_spec__0_spec__0(v_s_2742_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_IO_println___at___00Dsl_EmitPancake_main_spec__0(lean_object* v_s_2745_){
_start:
{
uint32_t v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = 10;
v___x_2748_ = lean_string_push(v_s_2745_, v___x_2747_);
v___x_2749_ = lp_orb_x2dcompiler_IO_print___at___00IO_println___at___00Dsl_EmitPancake_main_spec__0_spec__0(v___x_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_IO_println___at___00Dsl_EmitPancake_main_spec__0___boxed(lean_object* v_s_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = lp_orb_x2dcompiler_IO_println___at___00Dsl_EmitPancake_main_spec__0(v_s_2750_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_main(){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2759_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__0));
v___x_2760_ = lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk;
v___x_2761_ = l_IO_FS_writeFile(v___x_2759_, v___x_2760_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_dec_ref(v___x_2761_);
v___x_2762_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__1));
v___x_2763_ = lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk;
v___x_2764_ = l_IO_FS_writeFile(v___x_2762_, v___x_2763_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
lean_dec_ref(v___x_2764_);
v___x_2765_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__2));
v___x_2766_ = lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk;
v___x_2767_ = l_IO_FS_writeFile(v___x_2765_, v___x_2766_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
lean_dec_ref(v___x_2767_);
v___x_2768_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__3));
v___x_2769_ = lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk;
v___x_2770_ = l_IO_FS_writeFile(v___x_2768_, v___x_2769_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
lean_dec_ref(v___x_2770_);
v___x_2771_ = ((lean_object*)(lp_orb_x2dcompiler_Dsl_EmitPancake_main___closed__4));
v___x_2772_ = lp_orb_x2dcompiler_IO_println___at___00Dsl_EmitPancake_main_spec__0(v___x_2771_);
return v___x_2772_;
}
else
{
return v___x_2770_;
}
}
else
{
return v___x_2767_;
}
}
else
{
return v___x_2764_;
}
}
else
{
return v___x_2761_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_main___boxed(lean_object* v_a_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = lp_orb_x2dcompiler_Dsl_EmitPancake_main();
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* _lean_main(){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = lp_orb_x2dcompiler_Dsl_EmitPancake_main();
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_main___boxed(lean_object* v_a_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = _lean_main();
return v_res_2778_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Dsl_EmitPancake(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0 = _init_lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0();
lean_mark_persistent(lp_orb_x2dcompiler_Dsl_EmitPancake_regionC0);
lp_orb_x2dcompiler_Dsl_EmitPancake_boundscanExport = _init_lp_orb_x2dcompiler_Dsl_EmitPancake_boundscanExport();
lean_mark_persistent(lp_orb_x2dcompiler_Dsl_EmitPancake_boundscanExport);
lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice = _init_lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice();
lean_mark_persistent(lp_orb_x2dcompiler_Dsl_EmitPancake_serveSlice);
lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk = _init_lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk();
lean_mark_persistent(lp_orb_x2dcompiler_Dsl_EmitPancake_regionPnk);
lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk = _init_lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk();
lean_mark_persistent(lp_orb_x2dcompiler_Dsl_EmitPancake_machinePnk);
lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk = _init_lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk();
lean_mark_persistent(lp_orb_x2dcompiler_Dsl_EmitPancake_exportPnk);
lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk = _init_lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk();
lean_mark_persistent(lp_orb_x2dcompiler_Dsl_EmitPancake_servePnk);
return lean_io_result_mk_ok(lean_box(0));
}
char ** lean_setup_args(int argc, char ** argv);
void lean_initialize_runtime_module();
#if defined(WIN32) || defined(_WIN32)
#include <windows.h>
#endif
lean_object* run_main(int argc, char ** argv) {
    return _lean_main();
}
int main(int argc, char ** argv) {
#if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
#endif
  lean_object* res;
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  res = initialize_orb_x2dcompiler_Dsl_EmitPancake(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    lean_init_task_manager();
    res = lean_run_main(&run_main, argc, argv);
  }
  lean_finalize_task_manager();
  if (lean_io_result_is_ok(res)) {
    int ret = 0;
    lean_dec_ref(res);
    return ret;
  } else {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
}
#ifdef __cplusplus
}
#endif
